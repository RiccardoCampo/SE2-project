abstract sig  Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig CarState{}
one sig Reserved extends CarState{}
one sig Running extends CarState{}
one sig Malfunctioning extends CarState{}
one sig Available extends CarState{}
//sig InCharge extends CarState{}    maybe not needed


sig User{
	reserve: lone Car,
	drive: lone Car,
	drive_with: some User,
	is_passenger: one Bool,
	is_driver: one Bool
}

sig SafeArea{
	has_cars: some Car
}

sig Car {
	state: one CarState	
}

// WITH BOOL     not really needed as it doesn't solve any of the problems..
fact noDriverNotDriving{
// 	no driver with not driving car
	all u: User | u.is_driver = False || u.drive != none
//	no user driving car not being driver
	all u: User | u.is_driver = True || u.drive = none
}

fact noPassengerNotIndrive_with{
// no user in drive_with not passengers
	all u: User | u.is_passenger = False || u in User.drive_with
// no passengers not in drive_with
	all u: User | u.is_passenger = True || u not in User.drive_with
}

fact noCarRunningInSafeAreas{
	no c: Car | c.state = Running && c in SafeArea.has_cars
}

fact noUserReservedWithoutCarState{
	no c: Car | c.state != Reserved && c in User.reserve
}

fact drivableCars{
	no c: Car | c.state != Running && c in User.drive 
}

fact safeAreasNotSharingCars{
	no s1, s2: SafeArea | s1 != s2 && (s1.has_cars & s2.has_cars != none)
}

fact noSharedCar{
	no u1, u2: User | u1 != u2 && (u1.reserve = u2.reserve || u1.drive = u2.drive)
}


fact allReservedOrAvailableCarInSafeAreas {
	all c: Car | (c in SafeArea.has_cars ) || (c.state != Available && c.state != Reserved)
}

fact noBrokenCarReserved{
	all c: Car | c.state != Malfunctioning || c not in User.reserve
}

fact noCarRunningNoDriver{
	all c: Car | c.state != Running || c in User.drive 
}

fact noDrivingReserved{  
//	all u: User | u.reserve = none || u.drive = none   // => no more than 2 users (1 driving 1 reserving)
//	all u: User | u.is_driver = False || u.reserve = none // same..
}

fact maxPassengers{
	all u: User | #u.drive_with < 4
}

fact drive_withRules{
// No User passenger if driving/reserving
//	all u: User | (u.drive = none && u.reserve = none) || u not in User.drive_with // => no User
//	all u: User | u.is_driver = False || u.is_passenger = False // => same..

// Drive_with only if user is driving  

//	all u: User | (u.drive != none) || u.drive_with = none // => no User only reserving
//	all u: drive_with.User | u.is_driver = True // same
	
	all u: User | u.drive_with & u = none						// no self drive_with

//	no drive_with in common
//	all u1, u2: User | u1 = u2 || u1.drive_with & u2.drive_with = none // => no more than 1 passenger
}

pred show {
}

run show for 8
