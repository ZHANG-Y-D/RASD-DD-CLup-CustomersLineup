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
}


abstract sig Customer{

}


sig ClickCustomer extends Customer{
	
	Username: one UserName,
	ValidBooking: lone Booking,
	HistoryBooking: set Booking

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

	all c: ClickCustomer | c.ValidBooking not in c.HistoryBooking
	all disj c1, c2 : ClickCustomer | c1.ValidBooking != c2.ValidBooking 
	all disj c1, c2 : ClickCustomer | c1.HistoryBooking & c2.HistoryBooking = none 
	all disj c1, c2 : ClickCustomer | c1.ValidBooking not in c2.HistoryBooking

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


//All ClickCustomer's Booking must in BookingSchedule
fact AllBookingStoreInBookingSchedule{

	all c: ClickCustomer | some b: BookingSchedule.AllBooking | c.ValidBooking in TimePeriod.b
	all chb: ClickCustomer.HistoryBooking | some b: BookingSchedule.AllBooking | chb in TimePeriod.b

}


//All Ticket must be Different
fact AllTicketMustBeDifferent{

	all disj bc1, bc2: BrickCustomer | bc1.ValidTicket != bc2.ValidTicket
	all disj b1,b2: Booking | b1.ValidTicket != b2.ValidTicket
	all b: Booking | no bc: BrickCustomer | b.ValidTicket = bc.ValidTicket

}









pred show {

	#ClickCustomer  = 3
	#ClickCustomer.ValidBooking > 1
	#ClickCustomer.HistoryBooking > 3
	#TimePeriod.(BookingSchedule.AllBooking) > 1
	#BrickCustomer > 1
	#QueueSchedule.CustomerInStore > 2

}

run show for 8





//
//pred sendABooking(b:Booking, 
//				cc: ClickCustomer,
//				time: Timestamp, vd: Int, cib: set CategoriesItem, dp: String, avd: Int,ticket: Ticket){
//
//
//	
//	b.BookedVisitTime = time and
//	b.ExpectedVisitDuration = vd and
//	b.CategoriesIntendBuy = cib and
//	b.PlaceDepartureFrom = dp and
//	b.ActualVisitedDuration = avd and
//	b.ValidTicket = ticket
//
//}
