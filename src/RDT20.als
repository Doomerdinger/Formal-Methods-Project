// Milestone 2 - Formal Methods Project
// Alec Tiefenthal & Jacob Knispel
module RDT20

open util/ordering[State] as S
open util/ordering[Data] as ordData
open util/boolean

sig Data{}

abstract sig Packet {}

sig DataPacket extends Packet{
	data: one Data,
	checksum: one Bool
}

sig AcknowledgmentPacket extends Packet{
	ack: one Bool
}

sig Sender {
	data: set Data,
	packet: lone DataPacket,
	ackpckt: lone AcknowledgmentPacket
}

sig Receiver {
	data: set Data,
	packet: lone DataPacket,
	ackpckt: lone AcknowledgmentPacket
}

sig State {
	sender: one Sender,
	receiver: one Receiver
}

pred Sender.make_pkt[dt: Data, old_data: set Data] {
	one pck: DataPacket | pck.data = dt and pck.checksum = True and this.packet = pck
	this.data = old_data - this.packet.data
	this.ackpckt = none
}

//This states that the packet for this Receiver is the same
// as the packet in the specified sender, except that the checksum
// value may not be the same (modeling corruption)
pred Receiver.regen_pkt[sndr: Sender] {
	this.packet.data = sndr.packet.data
}

//Not a particularly nessecary pred, but it checks if the
// checksum value on this receiver is True.
pred Receiver.acknowledgment[] {
	boolean/isTrue[this.packet.checksum]
}

//Not a particularly nessecary pred, but it checks if the
// data on this receiver is the previous data in addition to
// the data in the packet.
pred Receiver.extract[pck: DataPacket, old_data: set Data] {
	this.data = old_data + pck.data
}

pred State.Init[] {
	this.sender.data = Data
	this.sender.packet = none
	this.sender.ackpckt = none
	
	#this.receiver.data = 0 //should be able to change to none
	this.receiver.packet = none
	this.receiver.ackpckt = none
}

pred State.End[] {
	#this.sender.data = 0 //should be able to change to none
	this.receiver.data = Data

	this.sender.ackpckt = none
	this.receiver.ackpckt = none
	this.sender.packet = none
	this.receiver.packet = none
}

pred Transition[s, s': State] {
	// s is waiting for send to convert data to packet
	(s.sender.packet = none and s.receiver.packet = none) =>
	//Data sent in order. Not specified, but it may make things 
	//easier in the future, and it just kinda makes sense for data transfer.
	{
		s'.sender.make_pkt[ordData/min[s.sender.data], s.sender.data]
		s'.sender.ackpckt = none
		s'.receiver.packet = none
		s'.receiver.data = s.receiver.data
		s'.receiver.ackpckt = none
	}

 	// s is waiting to send a packet, or just recieved an ackpckt and must determine what to do
	else (s.sender.packet != none and s.receiver.packet = none) =>
	{
		//If there is no ackpckt(waiting to send) or the ackpckt says that
		// the data was corrupted (False) then send the current packet again
		(s.sender.ackpckt = none or s.sender.ackpckt.ack = False) =>
		{
			s'.sender.packet = s.sender.packet
			//Send/regen packet to the receiver.
			//The regen takes a potentially different checksum value.
			s'.receiver.regen_pkt[s.sender]

			//If the checksum in the receiver is True, then store the data and
			// create an AcknowledgmentPacket with a True ack value.
			(s'.receiver.acknowledgment[]) =>
			{
				s'.receiver.extract[s'.receiver.packet, s.receiver.data]
				s'.receiver.ackpckt.ack = True
			}
			//Checksum is not True, do not store the data and create an
			// AcknowledgmentPacket with a False ack value.
			else {
				s'.receiver.data = s.receiver.data
				s'.receiver.ackpckt.ack = False
			}
		}
		//The sender has an AcknowledgmentPacket with an ack value
		// of false. Resent the current packet and remove the 
		// AcknowledgmentPacket from the sender.
		else
		{
			s'.sender.packet = none
			s'.receiver.packet = none
			s'.receiver.data = s.receiver.data
			s'.receiver.ackpckt = none
		}

		//These things happen no matter if a packet is resent, finished, or sent for the first time.
		s.receiver.ackpckt = none //should be able to remove this line
		s'.sender.ackpckt = none
		s'.sender.data = s.sender.data
	}

	//Both sender and receiver have packets, the receiver should have 
	// already processed the packet by now and generated an
	// AcknowledgmentPacket, send it to the Sender and remove
	// the AcknowledgmentPacket and the DataPacket from the Receiver.
	else (s.sender.packet != none and s.receiver.packet != none) =>
	{
		s'.sender.ackpckt = s.receiver.ackpckt
		s'.sender.packet = s.sender.packet
		s'.sender.data = s.sender.data

		s'.receiver.data = s.receiver.data
		s'.receiver.ackpckt = none
		s'.receiver.packet = none
	}
	s.next = s'
}

//Do nothing during this state.
pred Skip[s, s': State] {
	s.sender = s'.sender
	s.receiver = s'.receiver
}

fact {
	S/first.Init[] //Init the first State
	all s: State - (S/last) | //All States except the last one
		let s' = s.next |	//s' is the state after the one we are looking at
			(s.End[] => Skip[s, s'] //If the current state is done, the next state is the same
			else Transition[s, s']) //If the current state isn't done, then transition.
}

// --- Protocol properties ---

// 1. Possible (at least one way) to transmit all data in the sender's buffer to the receiver's buffer
pred transmitAllData {
	(S/last).End[]
}

// 2. Finds at least one way data cannot be transferred
assert canAlwaysTransferAllData {
	(S/last).End[]
}

run transmitAllData for 5 but 1 Data, 4 Sender, 3 Receiver, 2 Packet
check canAlwaysTransferAllData for 15 but 1 Data, 2 Receiver, 3 Sender, 3 Packet