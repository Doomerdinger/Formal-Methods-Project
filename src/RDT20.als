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
	//TODO: Need some way to represent a data checksum, requires additional data to be sent
}

sig AcknowledgmentPacket extends Packet{
	ack: one Bool
}



sig Sender {
	data: set Data,
	packet: lone DataPacket,
	ackpckt: lone AcknowledgmentPacket
	//TODO: If a negative acknowledgment is recieved, then send the packet again,
	//if a positive acknowledgment is recieved. send the next one.

	//Be sure to change the transition logic that immidiately gets rid of the packet
	//in the sender, as the last packet (or data, and regen the packet every time?)
	//now needs to be stored.
}

sig Receiver {
	data: set Data,
	packet: lone DataPacket,
	ackpckt: lone AcknowledgmentPacket
	//TODO: Positive and negative acknowledgment packets to be sent back to the
	//sender, depending on if the data checksum is correct
}

sig State {
	sender: one Sender,
	receiver: one Receiver
}

pred Sender.make_pkt[dt: Data, old_data: set Data] {
	one pck: DataPacket | pck.data = dt and pck.checksum = True and this.packet = pck
	this.data = old_data - this.packet.data
	this.ackpckt = none

	//Do I need to set the checksum? I don't think so, as it should be either t/f.
}

pred Receiver.regen_pkt[sndr: Sender] {
	this.packet.data = sndr.packet.data
	//Do I need to set the checksum? I don't think so, as it should be either t/f.
}

pred Receiver.acknowledgment[] {
	boolean/isTrue[this.packet.checksum]
}

pred Receiver.extract[pck: DataPacket, old_data: set Data] {
	//this.packet = none
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
	//No packets

	//Sender gen packet

	//Sender send packet, Receiver recieve packet, reciever parse packet
	// receiver generate ack packet
	// if no corruption then store data in reciever, clear the packets
	// if corruption, clear packets

	//reciever send ack, sender rec ack, if corruption, send datapacket again, if no, remove packets




	// s is waiting for send to convert data to packet
	(s.sender.packet = none and s.receiver.packet = none) =>
		//Data sent in order. Not specified, but it may make things 
		//easier in the future, and it just kinda makes sense for data transfer.
		{s'.sender.make_pkt[ordData/min[s.sender.data], s.sender.data]
		s'.sender.ackpckt = none
		s'.receiver.packet = none
		s'.receiver.data = s.receiver.data
		s'.receiver.ackpckt = none
		}

 	// s is waiting to send packet to receiver
	else (s.sender.packet != none and s.receiver.packet = none) =>
	{
		(s.sender.ackpckt = none or s.sender.ackpckt.ack = False) =>
		{
			s'.sender.packet = s.sender.packet

			s'.receiver.regen_pkt[s.sender]

			(s'.receiver.acknowledgment[]) =>
			{
				s'.receiver.extract[s'.receiver.packet, s.receiver.data]
				s'.receiver.ackpckt.ack = True
			}
			else {
				s'.receiver.data = s.receiver.data
				s'.receiver.ackpckt.ack = False
			}
		}
		else
		{
			s'.sender.packet = none
			s'.receiver.packet = none
			s'.receiver.data = s.receiver.data
			s'.receiver.ackpckt = none
		}

		s.receiver.ackpckt = none //should be able to be removed
		s'.sender.ackpckt = none
		s'.sender.data = s.sender.data
	}

	// s is waiting for receiver to convert packet to data
	else (s.sender.packet != none and s.receiver.packet != none) =>
	{
		s'.sender.ackpckt = s.receiver.ackpckt
		s'.sender.packet = s.sender.packet
		s'.sender.data = s.sender.data

		s'.receiver.data = s.receiver.data
		s'.receiver.ackpckt = none
		s'.receiver.packet = none
	}


		// s is waiting for send to convert data to packet
	/*(s.sender.packet = none and s.receiver.packet = none) =>
		//Data sent in order. Not specified, but it may make things 
		//easier in the future, and it just kinda makes sense for data transfer.
		{s'.sender.make_pkt[ordData/min[s.sender.data], s.sender.data]
		s'.receiver.packet = none
		s'.receiver.data = s.receiver.data
		}

 	// s is waiting to send packet to receiver
	else (s.sender.packet != none and s.receiver.packet = none) =>
		{s'.sender.packet = none
		s'.receiver.packet = s.sender.packet
		s'.receiver.data = s.receiver.data
		s'.sender.data = s.sender.data}

	// s is waiting for receiver to convert packet to data
	else (s.sender.packet = none and s.receiver.packet != none) =>
		{s'.sender.packet = none
		s'.receiver.extract[s.receiver.packet, s.receiver.data]
		s'.sender.data = s.sender.data}
		*/

	s.next = s'
}

pred Skip[s, s': State] {
	s.sender = s'.sender
	s.receiver = s'.receiver
}

fact {
	S/first.Init[]
	all s: State - (S/last) | 
		let s' = s.next |
			(s.End[] => Skip[s, s']
			else Transition[s, s'])
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

//#states = 3 * #data + 1
//#Sender/Receiver = 2 * #data + 1
run transmitAllData for 5 but 1 Data, 4 Sender, 3 Receiver, 2 Packet
check canAlwaysTransferAllData for 16 but 5 Data