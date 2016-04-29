// Milestone 1 - Formal Methods Project
// Alec Tiefenthal & Jacob Knispel
module RDT10

open util/ordering[State] as S
open util/ordering[Data] as ordData

sig Data{}

sig Packet{data: one Data}

sig Sender {
	data: set Data,
	packet: lone Packet
}
sig Receiver {
	data: set Data,
	packet: lone Packet
}

sig State {
	sender: one Sender,
	receiver: one Receiver
}

pred Sender.make_pkt[dt: Data, old_data: set Data] {
	one pck: Packet | pck.data = dt and this.packet = pck
	this.data = old_data - this.packet.data
}

pred Receiver.extract[pck: Packet, old_data: set Data] {
	this.packet = none
	this.data = old_data + pck.data
}

pred State.Init[] {
	this.sender.data = Data
	this.sender.packet = none
	
	#this.receiver.data = 0 //should be able to change to none
	this.receiver.packet = none
}

pred State.End[] {
	#this.sender.data = 0 //should be able to change to none
	this.receiver.data = Data
}

pred Transition[s, s': State] {

	// s is waiting for send to convert data to packet
	(s.sender.packet = none and s.receiver.packet = none) =>
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
run transmitAllData for 4 but 1 Data
check canAlwaysTransferAllData for 16 but 5 Data