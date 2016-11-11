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
one sig PassengersDiscount extends FeeVariator{
minPassengersNumber: one Int
}
one sig PlugDiscount extends FeeVariator{}
one sig BatteryDiscount extends FeeVariator{
minBatteryDiscount: one Int
}{
minBatteryDiscount <= 100
minBatteryDiscount >= 0
}
one sig FarorLowonBatteryMalus extends FeeVariator{
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
#unlockTime = 1 implies reservationTime.time < unlockTime.time
#ignitionTime = 1 implies unlockTime.time < ignitionTime.time && #unlockTime = 1
#endTime = 1 implies ignitionTime.time < endTime.time && #ignitionTime = 1
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

fact aReservedorBusyCarHasAlwaysARide {
all c: ElectricCar |(c.currentState in Reserved + Busy) implies  one r: Ride | r.car = c && rideisOngoing[r]
}

fact anOngoingRideHasACarReservedOrBusyAndViceVersa{
all r: Ride | #r.unlockTime = 0 && #r.endTime = 0 implies r.car.currentState = Reserved
all r: Ride | #r.unlockTime = 1 && #r.endTime = 0 implies r.car.currentState = Busy
all c: ElectricCar | c.currentState in (Busy + Reserved) implies one r: Ride | rideisOngoing[r]
}

fact aStartedCarisBusy{
all c: ElectricCar | c.engineOn = True implies c.currentState = Busy
}

fact no2CarsinTheSameSpot{
no disjoint c1, c2: ElectricCar | c1.currentPosition = c2.currentPosition
}

fact no2PGSinTheSameSpot{
no disjoint psg1, psg2: PowerGridStation | psg1.location = psg2.location
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

pred haveCarOrUserinCommon[r1: Ride, r2: Ride]{
r1.user = r2.user or r1.car = r2.car
}

pred rideisOngoing[r: Ride]{
#r.endTime = 0
}

pred reserveACar[ui: User, uf: User, ci: ElectricCar, cf: ElectricCar, r: Ride]{
no ride: Ride | (ride.user = ui or ride.car = ci) && rideisOngoing[ride]

r.car = cf && rideisOngoing[r] && cf.currentState = Reserved && r.user = uf
}

/*pred endARide[ri: Ride, rf: Ride]{
rideisOngoing[ri]

(!(rideisOngoing[ri])) && ri.car.currentState = Available
}*/

//Assertion

assert noUnavailableCarCanBeRent{
no r: Ride | r.car.currentState = Unavailable && rideisOngoing[r]
}

assert twoOngoingRidesImpliesTwoCarsAndTwoUsers{
all disjoint r1, r2: Ride | rideisOngoing[r1] && rideisOngoing[r2] implies r1.user != r2.user && r1.car != r2.car
}

assert allRidesAreConsecutive{
all disjoint r1, r2: Ride | haveCarOrUserinCommon[r1, r2] implies rideisOngoing[r1] && r2.endTime.time < r1.reservationTime.time or  rideisOngoing[r2] && r1.endTime.time < r2.reservationTime.time or !(rideisOngoing[r1] or rideisOngoing[r2]) && (r2.endTime.time < r1.reservationTime.time or r1.endTime.time < r2.reservationTime.time)
}

assert unavailableCarCannotStart{
all c: ElectricCar | c.currentState = Unavailable implies c.engineOn = False
}

check unavailableCarCannotStart
//pred show() {}

//run show for 8 but exactly 2 Ride, exactly 1 ElectricCar
