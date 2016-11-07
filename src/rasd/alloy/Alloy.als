open util/boolean

//Signatures

sig Array{}

sig DateTime {
time: one Int
}{
time >= 0
}

abstract sig CarState{}
one sig Available extends CarState{}
one sig Unavailable extends CarState{}
one sig Reserved extends CarState{}
one sig Busy extends CarState{}

sig Position{
latitude: one Int,
longitude: one Int
}

sig ElectricCar{
licencePlate: one Array,
batteryLevel: one Int,
currentPosition: one Position,
currentState: one CarState,
seatsNumber: one Int,
engineOn: one Bool
}{
batteryLevel >= 0
batteryLevel <= 100
seatsNumber > 0
}

sig SafeArea{
center: one Position,
radius: one Int
}

sig PowerGridStation{
location: one Position,
plugs: set Plug
}

sig Plug{
busy: one Bool
}

sig User{
taxCode: one Array,
email: one Array,
password: one Array,
name: one Array,
surname: one Array,
birthDate: one DateTime,
birthPlace: one Array
}

abstract sig FeeVariator{
feeVariatorPercentage: one Int
}{
feeVariatorPercentage <= 100
}
sig PassengersDiscount extends FeeVariator{
minPassengersNumber: one Int
}
sig PlugDiscount extends FeeVariator{}
sig BatteryDiscount extends FeeVariator{
minBatteryDiscount: one Int
}{
minBatteryDiscount <= 100
minBatteryDiscount >= 0
}
sig FarorLowonBatteryMalus extends FeeVariator{
maxBatteryLevel: one Int,
minDistancefromPGS: one Int
}{
maxBatteryLevel <= 100
maxBatteryLevel >= 0
}

sig Ride{
user: one User,
car: one ElectricCar,
reservationTime: one DateTime,
unlockTime: lone DateTime,
ignitionTime: lone DateTime,
endTime: lone DateTime,
maxPassengersNumber: one Int,
feeVariator: set FeeVariator
}{
reservationTime.time < unlockTime.time
unlockTime.time < ignitionTime.time
ignitionTime.time < endTime.time
maxPassengersNumber >= 0
maxPassengersNumber <= car.seatsNumber
}


//Facts

fact no2CarsWithTheSamePlate{
no disjoint c1, c2: ElectricCar | c1.licencePlate = c2.licencePlate
}

fact no2SimilarUsers{
no disjoint u1, u2: User | u1.email = u2.email or u1.taxCode = u2.taxCode or u1.password = u2.password
}

fact twoRidesImpliesTwoCarsAndTwoUsers{
no disjoint r1, r2: Ride | r1.user = r2.user or r1.car = r2.car
}

fact aReservedorBusyCarHasAlwaysARide {
all c: ElectricCar |(c.currentState in Reserved + Busy) <=>  one r: Ride | r.car = c
}

fact unavailableCarCannotStart{
all c: ElectricCar | c.currentState = Unavailable => c.engineOn = False
}

fact aStartedCarisBusy{
all c: ElectricCar | c.engineOn = True => c.currentState = Busy
}

fact no2CarsinTheSameSpot{
no disjoint c1, c2: ElectricCar | c1.currentPosition = c2.currentPosition
}

fact no2PGSinTheSameSpot{
no disjoint psg1, psg2: PowerGridStation | psg1.location = psg2.location
}

fact noUnavailableCarCanBeRent{
no r: Ride | r.car.currentState = Unavailable
}

fact noPassengersGreaterthanSeatsNumber{
no r: Ride | r.maxPassengersNumber > r.car.seatsNumber
}

fact eachPGSinaSA{
all psg: PowerGridStation | one sa: SafeArea | positionInSA[psg.location, sa]
}

//Predicates

pred positionInSA[p: Position, sa: SafeArea]{
plus[mul[sub[p.latitude, sa.center.latitude], sub[p.latitude, sa.center.latitude]], mul[sub[p.latitude, sa.center.latitude], sub[p.latitude, sa.center.latitude]]] <= mul[sa.radius, sa.radius]
}



pred show() {}
run show for 10 but exactly 5 ElectricCar, exactly 2 Ride
