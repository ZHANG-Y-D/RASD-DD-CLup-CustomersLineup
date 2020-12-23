sig TimePeriod{ }

sig UserName{ }

sig Ticket{ }

sig Booking{
	BookedVisitTime: one TimePeriod,
	ValidTicket: lone Ticket
}


one sig QueueSchedule{

	MaximumCustomerInStor: Int,
	CustomerInStore: set Customer,
	CurrentQueue: set Customer

}{

	MaximumCustomerInStor >= 0

	// CustomerInStore must be less than or equal to MaximumCustomerInStor
	#CustomerInStore <= MaximumCustomerInStor

	//One customer can only appear one time in QueueSchedule
	CustomerInStore & CurrentQueue = none

}


abstract sig Customer{

}


sig ClickCustomer extends Customer{
	
	Username: one UserName,
	ValidBooking: lone Booking,
	HistoryBooking: set Booking

}{

	//Hostory Booking must have Valid Ticket
	all hb: HistoryBooking | hb.ValidTicket != none

}

sig BrickCustomer extends Customer{

	ValidTicket: one Ticket

}

one sig BookingSchedule{

	AllBooking: TimePeriod -> set Booking,
	MaximumBookingInEachTimePeriod: Int

}{

	//Each TimePeriod's booking less than Maximum value
	all tp: TimePeriod | #tp.AllBooking <= MaximumBookingInEachTimePeriod

}



//The intersection of ValidBooking and HistoryBooking must be empty
fact VaildHistoryBookingMustBeDifferent{

	all c: ClickCustomer | c.ValidBooking != none and c.HistoryBooking != none => 
		c.ValidBooking not in c.HistoryBooking

	all disj c1, c2 : ClickCustomer | c1.ValidBooking != none and c2.ValidBooking != none =>  
		c1.ValidBooking != c2.ValidBooking 

	all disj c1, c2 : ClickCustomer | c1.HistoryBooking != none and c2.HistoryBooking  != none => 
		c1.HistoryBooking & c2.HistoryBooking = none 

	all disj c1, c2 : ClickCustomer | c1.ValidBooking != none and c2.HistoryBooking  != none =>
		c1.ValidBooking not in c2.HistoryBooking

}


//Each Click Customer's username must be different
fact UniqueUsername{
	
	all disj c1, c2 : ClickCustomer | c1.Username != c2.Username

}


fact noUselessUsername{

	 all u : UserName | one cc : ClickCustomer | u = cc.Username
}


fact noUselessBooking{

	all b : Booking | some  bsa: BookingSchedule.AllBooking | b in TimePeriod.bsa

}

fact noUselessTicket{

	all t : Ticket | some b: Booking | some bc: BrickCustomer  | 
		t = b.ValidTicket or t = bc.ValidTicket

}


//All ClickCustomer's Booking must in BookingSchedule
fact AllBookingStoreInBookingSchedule{

	all c: ClickCustomer | some b: BookingSchedule.AllBooking | c.ValidBooking in TimePeriod.b
	all chb: ClickCustomer.HistoryBooking | some b: BookingSchedule.AllBooking | chb in TimePeriod.b

}

//All BookingSchedule's Booking must in  ClickCustomer's Booking
fact AllBookingScheduleBookingMustInClickCustomerBooking{

	all b: TimePeriod.(BookingSchedule.AllBooking) | 
		some c: ClickCustomer | b = c.ValidBooking or b in c.HistoryBooking

}



//All Ticket must be Different
fact AllTicketMustBeDifferent{

	all disj bc1, bc2: BrickCustomer | bc1.ValidTicket != bc2.ValidTicket
	all disj b1,b2: Booking | b1.ValidTicket != b2.ValidTicket
	all b: Booking | no bc: BrickCustomer | b.ValidTicket != none => b.ValidTicket = bc.ValidTicket

}

//All Click Customer in QueueSchedule must have a valid booking with a valid ticket
fact ClickCustomerInQueueScheduleMustHaveValidBookingWithValidTicket{

	all cicq : QueueSchedule.CurrentQueue |  
		cicq in ClickCustomer => cicq.ValidBooking != none and 
		(cicq.ValidBooking).ValidTicket != none
	
	all cis : QueueSchedule.CustomerInStore |  
		cis in ClickCustomer => cis.ValidBooking != none and 
		(cis.ValidBooking).ValidTicket != none

}


//Cause the BrickCustomer's property, so they must always be in the QueueSchedule.
fact BrickCustomerMustBeInQueueSchedule{
	
	all bc: BrickCustomer | 
	some is: QueueSchedule.CustomerInStore | 
	some cq: QueueSchedule.CurrentQueue |
		(bc in is or bc in cq)

}


pred BrickCustomer{
	
	#BrickCustomer = 5
	#ClickCustomer = 0
	#Booking = 0
	
}

run BrickCustomer for 10



pred ClickCustomer {

	#ClickCustomer  > 1
	one c: ClickCustomer | c.ValidBooking = none and #c.HistoryBooking = 0
	one c: ClickCustomer | c.ValidBooking != none and #c.HistoryBooking = 0
	some c: ClickCustomer | c.ValidBooking != none and #c.HistoryBooking > 1
	#TimePeriod.(BookingSchedule.AllBooking) > 1
	#BrickCustomer = 1
	#QueueSchedule.CustomerInStore > 1
	#QueueSchedule.CurrentQueue > 1

}

run ClickCustomer for 10


pred show {

	#ClickCustomer > 3
	#ClickCustomer.ValidBooking > 1
	#ClickCustomer.HistoryBooking > 3
	#TimePeriod.(BookingSchedule.AllBooking) > 1
	#BrickCustomer > 3
	#QueueSchedule.CustomerInStore > 2

}

run show for 10
