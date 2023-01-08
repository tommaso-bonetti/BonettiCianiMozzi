// SIGNATURES
abstract sig Actor {}

sig User extends Actor {
    vehicles:   some ElectricVehicle,
    accounts:   some BankAccount
}

abstract sig Company extends Actor {
    accounts:   some BankAccount
}

sig CPO extends Company {
    stations:   some ChargingStation,
    stock:      one Int
}{
    stock > 0
}

sig DSO extends Company {
    prices: some Int
}{
    all p: Int | p in prices implies p > 0
}

sig ElectricVehicle {
    plate:      one Identifier,
    battery:    one BatteryLevel
}

sig ChargingStation {
    sockets:    some Socket,
    batteries:  set BatteryLevel
}

abstract sig BatteryLevel {}
one sig LOW, MID, HIGH extends BatteryLevel {} // L: 0%-33%, M: 34%-66%, H: 67%-100%

sig Socket {
    type:           one SocketType,
    cost:           one Int,
    connection:     lone ElectricVehicle,
    reservations:   set Booking
}{
    cost > 0
}

abstract sig SocketType {}
one sig SLOW, FAST, RAPID extends SocketType {}

sig Timeframe {
    start:  one Int,
    end:    one Int
}

sig Booking {
    customer:   one User,
    slot:       one Timeframe
}

sig BankAccount {
    money:  one Int
}

sig Identifier {}

// FACTS
fact User_Vehicle_Relationship {
    all v: ElectricVehicle | (one u: User | v in u.vehicles)
}

fact Actor_Bank_Relationship {
    all a: BankAccount | ((one u: User | a in u.accounts) && (no c: Company | a in c.accounts)) || ((no u: User | a in u.accounts) && (one c: Company | a in c.accounts)) // Logical XOR.
}

fact CPO_ChargingStation_Relationship {
    all c: ChargingStation | #{cpo: CPO | c in cpo.stations} >= 1
}

fact CS_CSS_Relationship {
    all css: Socket | (one cs: ChargingStation | css in cs.sockets)
}

fact Vehicle_Id_Relationship {
    all id: Identifier | #{v: ElectricVehicle | v.plate = id} >= 1
}

fact Socket_Booking_Relationship {
    all b: Booking | #{s: Socket | b in s.reservations} >= 1
}

fun OverlappingBookings (s: Socket, t: Booking) : set Booking {
    {b: Booking | b != t && b in s.reservations && (b.slot.start <= t.slot.end && b.slot.end >= t.slot.start)}  // Set comprehension.
}

fact NoOverlappings {
    all s: Socket, b: Booking | b in s.reservations implies #OverlappingBookings[s, b] = 0
}

fact PresentTimeWorldConsistency {
    all s: Socket, b: Booking | (b in s.reservations && b.slot.start = 0) implies (one v: ElectricVehicle, u: User | s.connection = v && b.customer = u && v in u.vehicles)
}

fact NoUbiquity {
    all v: ElectricVehicle | no disj s1, s2: Socket | v in s1.connection && v in s2.connection
}

fact Timeframe_Booking_Relationship {
    all t: Timeframe | #{b: Booking | t = b.slot} >= 1
}

fact ValidTimeframe {
    all t: Timeframe | t.start >= 0 && t.start < t.end
}

fact NoBankruptcy {
    no a: BankAccount | a.money < 0
}

// WORLDS
pred World {
    #User = 3
    #CPO >= 2
    #DSO = 1
    #ChargingStation >= 3
    #Socket >= 3
    #Booking >= 3
    all u: User | #u.accounts = 1 && all c: Company | #c.accounts = 1   // CONSTRAINT: BankAccount multiplicity
    all c: ChargingStation | (one cpo: CPO | c in cpo.stations)         // CONSTRAINT: CPO_ChargingStation_Relationship
    all id: Identifier | (one v: ElectricVehicle | v.plate = id)        // CONSTRAINT: Vehicle_Id_Relationship
    no disj v1, v2: ElectricVehicle | v1.plate = v2.plate               // CONSTRAINT: ElectricVehicle car licence plates
}
run World for 8

// DYNAMIC MODELING
pred Socket_Unchanged (s, s': Socket) {
    s.type = s'.type && s.cost = s'.cost && (one c: ChargingStation | s in c.sockets && s' in c.sockets)
}

pred User_Socket_Interaction_C (u: User, t: Timeframe, b: Booking, s, s': Socket) {
    /* The user reserves a socket, providing a timeframe. The bookings of the socket are updated. */
    b.customer = u && b.slot = t && b not in s.reservations && s'.reservations = s.reservations + b && Socket_Unchanged[s, s']
}

pred User_Socket_Interaction_D (u: User, t: Timeframe, b: Booking, s, s': Socket) {
    /* The user cancels a reservation. The bookings of the socket are updated. */
    b.customer = u && b.slot = t && b in s.reservations && s'.reservations = s.reservations - b && Socket_Unchanged[s, s']
}

pred User_Unchanged (u, u': User, v, v': ElectricVehicle, U_Bank, U_Bank': BankAccount) {
    u.vehicles - v = u'.vehicles - v' && u.accounts - U_Bank = u'.accounts - U_Bank'
}

pred CPO_Unchanged (cpo, cpo': CPO, CPO_Bank, CPO_Bank': BankAccount) {
    cpo.stations = cpo'.stations && cpo.accounts - CPO_Bank = cpo'.accounts - CPO_Bank'
}

pred Charge (v, v': ElectricVehicle) {
    (v.battery = LOW implies (v'.battery = MID || v'.battery = HIGH)) && ((v.battery = MID || v.battery = HIGH) implies v'.battery = HIGH)
}

pred Disconnection (v, v': ElectricVehicle, s, s': Socket) {
    (v in s.connection && v not in s'.connection) && (v' not in s.connection && v' not in s'.connection)
}

pred MoneyTransfer_User_CPO (u, u': User, cpo, cpo': CPO, U_Bank, U_Bank', CPO_Bank, CPO_Bank': BankAccount, cost: Int) {
    U_Bank in u.accounts && U_Bank' in u'.accounts && CPO_Bank in cpo.accounts && CPO_Bank' in cpo'.accounts && minus[U_Bank.money, cost] >= 0 && U_Bank'.money = minus[U_Bank.money, cost] && CPO_Bank'.money = plus[CPO_Bank.money, cost]
}

pred User_CPO_Interaction (v, v': ElectricVehicle, u, u': User, s, s': Socket, cpo, cpo': CPO, U_Bank, U_Bank', CPO_Bank, CPO_Bank': BankAccount) {
    /* After a charge, the user pays for the service. */
    v in u.vehicles && v' in u'.vehicles && v != v' && v.plate = v'.plate && Charge[v, v'] && Disconnection[v, v', s, s'] && MoneyTransfer_User_CPO[u, u', cpo, cpo', U_Bank, U_Bank', CPO_Bank, CPO_Bank', s.cost] && User_Unchanged[u, u', v, v', U_Bank, U_Bank'] && Socket_Unchanged[s, s'] && (CPO_Unchanged[cpo, cpo', CPO_Bank, CPO_Bank'] && cpo.stock = cpo'.stock)
}

pred DSO_Unchanged (dso, dso': DSO, DSO_Bank, DSO_Bank': BankAccount) {
    dso.prices = dso'.prices && dso.accounts - DSO_Bank = dso'.accounts - DSO_Bank'
}

pred EnergyTransfer_CPO_DSO (cpo, cpo': CPO, energy: Int) {
    energy > 0 && cpo'.stock = plus[cpo.stock, energy]
}

pred MoneyTransfer_CPO_DSO (cpo, cpo': CPO, dso, dso': DSO, CPO_Bank, CPO_Bank', DSO_Bank, DSO_Bank': BankAccount, price: Int) {
    price in dso.prices && CPO_Bank in cpo.accounts && CPO_Bank' in cpo'.accounts && DSO_Bank in dso.accounts && DSO_Bank' in dso'.accounts && minus[CPO_Bank.money, price] >= 0 && CPO_Bank'.money = minus[CPO_Bank.money, price] && DSO_Bank'.money = plus[DSO_Bank.money, price]
}

pred CPO_DSO_Interaction (cpo, cpo': CPO, dso, dso': DSO, e, p: Int, CPO_Bank, CPO_Bank', DSO_Bank, DSO_Bank': BankAccount) {
    /* The CPO buys energy from a DSO. */
    EnergyTransfer_CPO_DSO[cpo, cpo', e] && MoneyTransfer_CPO_DSO[cpo, cpo', dso, dso', CPO_Bank, CPO_Bank', DSO_Bank, DSO_Bank', p] && CPO_Unchanged[cpo, cpo', CPO_Bank, CPO_Bank'] && DSO_Unchanged[dso, dso', DSO_Bank, DSO_Bank']
}

// DYNAMIC ANALYSIS
pred Dyn_User_Socket_Interaction_C (u: User, t: Timeframe, b: Booking, s, s': Socket) {
    User_Socket_Interaction_C[u, t, b, s, s']
    all v: ElectricVehicle | (one u: User | v in u.vehicles)
    no disj v1, v2: ElectricVehicle | v1.plate = v2.plate
}
run Dyn_User_Socket_Interaction_C

pred Dyn_User_Socket_Interaction_D (u: User, t: Timeframe, b: Booking, s, s': Socket) {
    User_Socket_Interaction_D[u, t, b, s, s']
    all v: ElectricVehicle | (one u: User | v in u.vehicles)
    no disj v1, v2: ElectricVehicle | v1.plate = v2.plate
}
run Dyn_User_Socket_Interaction_D

assert CD_Ops_Interaction {
    all s, s', s'': Socket, u: User, t: Timeframe, b: Booking | User_Socket_Interaction_C[u, t, b, s, s'] && User_Socket_Interaction_D[u, t, b, s', s''] implies s.reservations = s''.reservations
}
check CD_Ops_Interaction

run User_CPO_Interaction for 8

run CPO_DSO_Interaction for 8