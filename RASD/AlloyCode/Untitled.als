//abstract sig Bool {}
//one sig True extends Bool {} 
//one sig False extends Bool {}


abstract sig Customer{

}

sig ClickCustomer extends Customer{
	
	Username: String,
	Password: String,
	ValidBooking: lone Booking,
	HistoryBooking: set Booking

}

sig BrickCustomer extends Customer{

	ValidTicket: one Ticket

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

sig Booking{
	BookedVisitTime: one Timestamp,
	ExpectedVisitDuration: Int,
	CategoriesIntendBuy: set CategoriesItem,
	PlaceDepartureFrom: String,
	ActualVisitedDuration: Int,
	ValidTicket: lone Ticket
}{
	ExpectedVisitDuration > 0
	ActualVisitedDuration > 0
	#CategoriesIntendBuy > 0
}

sig Ticket{
	QRCode: String,
	EstimatedDepartureTime: one Timestamp,
	QueueNumber: Int,
	StorePlannedRoadmap: String

}

sig CategoriesItem{
	Name: String
}


one sig BookSchedule{
	AllBooking: Timestamp -> set Booking
}

//
//sig DailyBooking{
//	Date: one Date, 
//	TodayBooking: set Booking,
//	TodayMaxBookingInEveryHour: Int
//}


sig Date{ 
	Day: one Int, 
	Month: one Int, 
	Year: one Int
}{
	Day > 0 
	Day <= 31
	Month > 0
	Month <= 12
	Year > 1980
}


sig Timestamp{
	Date: one Date,
	Hour: one Int, 
	Minute: one Int

}{
	Hour >= 0
	Hour  < 24
	Minute >= 0 
	Minute < 60
}

//Every Booking corresponds to a Click Customer
fact BookingCorrespondsClickCustomer{

	all b: Booking | some cc: ClickCustomer | b = cc.ValidBooking or b in cc.HistoryBooking
}

//Each Ticket corresponds to either a Brick Customer or Click Customer's Booking
fact TicketCorrespondsBrickCustomerOrBooking{

	all t: Ticket | some bc: BrickCustomer | some b: Booking | t = bc.ValidTicket or t = b.ValidTicket

}

//Each Booking must be found in DailyBooking
//fact BookingInDailyBooking{
//
//	all b:Booking | some db: DailyBooking | b in db.TodayBooking
//
//}

//Each Booking in DailyBooking corresponds to a Click Customer
//fact DailyBookingCorrespondsClickCustomer{
//
//	all cc: ClickCustomer | some db: DailyBooking | cc.ValidBooking != none iff (cc.ValidBooking in db.TodayBooking)
//	all  cc: ClickCustomer  | some db: DailyBooking |
//		(cc.HistoryBooking != none) iff (cc.HistoryBooking & db.TodayBooking = cc.HistoryBooking)
//}

//Each Click Customer's username must be different
fact UniqueUsername{
	
	all disj c1, c2 : ClickCustomer | c1.Username != c2.Username

}

//Each Item name must be different
fact UniqueCategoriesItem{

	all disj ci1, ci2 : CategoriesItem | ci1.Name != ci2.Name
}


//The intersection of ValidBooking and HistoryBooking must be empty
fact VaildHistoryBookingMustBeDifferent{

	 all c: ClickCustomer | c.ValidBooking & c.HistoryBooking = none

}


//The intersection of CustomerInStore and CurrentQueue must be empty
fact ACustomerIsEitherInStoreOrInQueue{

	all qs: QueueSchedule | qs.CustomerInStore & qs.CurrentQueue = none

}


//Each Booking's EstimatedDepartureTime is earlier than BookedVisitTime in the Ticket, and in the same day.
fact DepartTimeEarlierThanBookedVisitTime{

	all disj t1, t2: Timestamp | ( all b: Booking, t: b.ValidTicket | 
		(t1 = b.BookedVisitTime && t2 = t.EstimatedDepartureTime) => 
		(t1.Date = t2.Date && (t1.Hour < t2.Hour || (t1.Hour = t2.Hour && t1.Minute < t2.Minute))))
	
}


//All Customer in QueueSchedule must have valid Booking
fact CustomerInQueueScheduleWithValidBooking{

	all c: Customer, qs: QueueSchedule | 
		(c in qs.CustomerInStore || c in qs.CurrentQueue) => c.ValidBooking != none

}


//Customer's valid and history Booking must in DailyBooking
//fact AllBookingInDailyBooking{
//
//	all c: Customer, db: DailyBooking | (c.ValidBooking in db.TodayBooking) &&
//		 (c.HistoryBooking & db.TodayBooking = c.HistoryBooking)
//
//}

//Each Ticket refers to only one Customer or Booking
fact TicketRefersToUniqueCustomer{

	all disj b1, b2: Booking, disj bc1, bc2: BrickCustomer | 
		b1.ValidTicket & b2.ValidTicket & bc1.ValidTicket & bc2.ValidTicket = none

}




//Each hour's booking is less than Max
//fact BookingLessThanMax{
//	
//
//
//}


pred ClickCustomerRegister(cc: ClickCustomer,u: String, p: String){
	cc.Username = u 
	cc.Password = p
}

//run ClickCustomerRegister


pred sendABooking(b:Booking, 
				cc: ClickCustomer,
				time: Timestamp, vd: Int, cib: set CategoriesItem, dp: String, avd: Int,ticket: Ticket){


	
	b.BookedVisitTime = time and
	b.ExpectedVisitDuration = vd and
	b.CategoriesIntendBuy = cib and
	b.PlaceDepartureFrom = dp and
	b.ActualVisitedDuration = avd and
	b.ValidTicket = ticket

}
//run sendABooking


pred show(){
	

	#BrickCustomer >= 1
	#ClickCustomer >= 1
	#QueueSchedule = 1
	#Booking >= 2
	#Ticket >= 2
	#CategoriesItem >= 1
	#BookSchedule = 1

}

//run show for 3 
