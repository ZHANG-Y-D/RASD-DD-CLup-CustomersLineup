abstract sig Bool {}
one sig True extends Bool {} 
one sig False extends Bool {}


abstract sig Customer{

}


sig ClickCustomer extends Customer{
	
	Username: String,
	Password: String,
	ValidBooking: lone Booking,
	HistoryBooking: set Booking,
	IsLongTermCustomer: one Bool

}


sig BrickCustomer extends Customer{

	ValidTicket: lone Ticket

}



one sig QueueSchedule{
	MaximumCustomerInStor: Int,
	CustomerInStore: set Customer,
	CurrentQueue: set Customer
}{

	MaximumCustomerInStor >= 0
	#CustomerInStore >= 0
	#CurrentQueue >= 0

	// CustomerInStore must be less than or equal to MaximumCustomerInStor
	#CustomerInStore <= MaximumCustomerInStor

}

sig Booking{
	BookedVisitTime: one Timestamp,
	ExpectedVisitDuration: Int,
	CategoriesIntendBuy: set CategoriesItem,
	PlaceDepartureFrom: String,
	ActualVisitedDuration: Int
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
}{
	//Each Name must be different

}


one sig BookSchedule{
	AllBooking: set DailyBooking
}


sig DailyBooking{
	Date: seq Date, //??
	TodayBooking: set Booking,
	TodayMaxBookingInEachTimePeriod: Int
}{
	//The number of Booking in each time period cannot exceed the TodayMaxCustomerInStore

	
}


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
	Minute: one Int, 
	Second: one Int 
}{
	Hour >= 0
	Hour  < 24
	Minute >= 0 
	Minute < 60
	Second >= 0
	Second < 60
}


//Each Click Customer's username must be different
fact UniqueUsername{
	
	all disj c1, c2 : ClickCustomer | c1.Username != c2.Username
}


//The intersection of ValidBooking and HistoryBooking must be empty
fact VaildHistoryBookingMustBeDifferent{

	 all c: ClickCustomer | no c.ValidBooking & c.HistoryBooking 
}

//The intersection of CustomerInStore and CurrentQueue must be empty
fact ACustomerIsEitherInStoreOrInQueue{

	all qs: QueueSchedule | no qs.CustomerInStore & qs.CurrentQueue
}

//The customer's EstimatedDepartureTime is earlier than BookedVisitTime
fact DepartTimeEarlierThanBookedVisitTime{

	all c: ClickCustomer | c.ValidTicket.EstimatedDepartureTime.

}


//The valid booking time cannot overlap
fact NoTimeOverlapFromValidBooking{
	
	

}


//All Customer in QueueSchedule must have at least one valid Booking
fact CustomerInQueueScheduleWithValidBooing{

}


//Customer's valid and history Booking must in DailyBooking
fact AllBooingInDailyBooking{

}

//each Ticket refers to only one Customer
fact TicketRefersToUniqueCustomer{

}


//If a customer has some History Booking with average ActualVisitedDuration longer than 1 hour, then the this customer is LongTermCustomer
assert LongTermCustomerHaveLongAverageDuration{

}



pred sendABooking{

}




