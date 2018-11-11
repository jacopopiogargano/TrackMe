-- SIGNATURES 

sig Individual{
	age: one Int
}{age >=0 }

one sig Data4Help{
	userdata: Data one -> one User,
	groupdata: Data -> AnonUsersGroup
}

sig HealthData{
	timestamp: one Int,
	data: one Data
}{timestamp>0}

sig Position{
	timestamp: one Int,
	data: one Data,
	lat: one Int,
	long: one Int
}{timestamp>0}

sig Data {
	healthData: set HealthData,
	positions: set Position
}

sig User {
	individual: one Individual
}

sig AnonUsersGroup {
	filter: one Filter
}

sig Filter{
	age: one Int
}

sig Service{
	thirdParty: one ThirdParty,
	users: set User,
	subscribedUsers: set User
}{subscribedUsers in users}

sig ThirdParty {
	services: set Service,
	userdata: Data lone -> lone User,
	groupdata: Data -> AnonUsersGroup
}{services.users = Data.userdata}

-- FUNCTIONS

fun retrieveUserData[d4h: Data4Help, u: User] : Data->User {
	d4h.userdata :> u
}

fun getAllDataOfAnonUsersGroup[d4h: Data4Help, aug: AnonUsersGroup] : set Data {
	(d4h.groupdata).aug
}

fun getAllUsersFromAnonUsersGroup[d4h: Data4Help, aug: AnonUsersGroup] : set User{
	(getAllDataOfAnonUsersGroup[d4h, aug]).(d4h.userdata)
}

fun retrieveDataToAnonUsersGroupByGroup[d4h: Data4Help, aug:  AnonUsersGroup] :
	Data -> AnonUsersGroup{
	d4h.groupdata :> aug
}

-- FACTS

fact userIndividualRelationshipIsUnique{
	all disj u1, u2:User, i:Individual |
	not (u1.individual = i and u2.individual = i)
}

fact healthDataToDataConnection{
	all d:Data, hd: HealthData | 
	hd in d.healthData iff hd.data = d
}

fact postionToDataConnection{
	all d:Data, p: Position | 
	p in d.positions iff p.data = d
}

fact userdataInThirdPartyImpliesUserdataInData4Help {
	all d:Data, u: User, d4h:Data4Help, tp:ThirdParty |
	d->u in tp.userdata implies d->u in d4h.userdata
}

fact allHealthDataBelongsToOnlyOneData{
	all hd: HealthData | all disj d1,d2: Data |
	not (hd in d1.healthData and hd in d2.healthData)
}

fact allPositionBelongsToOnlyOneData{
	all p:Position | all disj d1,d2: Data |
	not (p in d1.positions and p in d2.positions)
}

fact serviceCanBeOfOnlyOneThirdParty{
	all s:Service | all disj t1,t2: ThirdParty |
	not (s in t1.services and s in t2.services)
}

fact serviceThirdPartyRelationshipIsUnique{
	all s:Service, tp:ThirdParty |
	s.thirdParty = tp iff s in tp.services
}

fact anonUsersGroupsAreMadeUpOfMoreThan2Users {
	all aug: AnonUsersGroup, d4h: Data4Help |
	#(getAllUsersFromAnonUsersGroup[d4h, aug]) > 2
	-- #(getAllUsersFromAnonUsersGroup[d4h, aug]) >= 1000
}

fact anonUsersGroupsAreMadeOfUsersThatRespectFilter {
	all aug: AnonUsersGroup, d4h: Data4Help |
	(getAllUsersFromAnonUsersGroup[d4h, aug]).individual.age = aug.filter.age
}

fact dataIsOfAnonUsersGroup {
	all tp:ThirdParty, aug: AnonUsersGroup, d4h: Data4Help |
	aug in Data.(tp.groupdata) implies getAllDataOfAnonUsersGroup[d4h, aug]
		in tp.groupdata.AnonUsersGroup
}

-- PREDICATES

pred sendUserData [u: User, s: Service, tp:ThirdParty, tp': ThirdParty, d4h: Data4Help] {
	u in s.users
	tp = s.thirdParty
	tp'.services = tp.services
	tp'.groupdata = tp.groupdata
	tp'.userdata = tp.userdata + retrieveUserData[d4h, u]
}

pred sendGroupData [f: Filter, s: Service, tp:ThirdParty, tp': ThirdParty, d4h: Data4Help,
	aug: AnonUsersGroup] {
	aug in Data.(d4h.groupdata)
	f in aug.filter
	tp = s.thirdParty
	tp'.services = tp.services
	tp'.userdata = tp.userdata
	tp'.groupdata = tp.groupdata + retrieveDataToAnonUsersGroupByGroup[d4h,aug]
}

pred show {}

-- ASSERTIONS

assert sendUserDataOkay{
	all tp', tp: ThirdParty, u:User, s:Service, d4h:Data4Help |
	retrieveUserData[d4h,u] not in tp.userdata and sendUserData[u, s, tp, tp', d4h]
		implies retrieveUserData[d4h, u] in tp'.userdata
}

assert sendGroupDataOkay{
	all tp,tp': ThirdParty, f: Filter, s: Service, d4h: Data4Help, aug: AnonUsersGroup |
	sendGroupData[f, s, tp, tp', d4h, aug] implies ( aug in Data.(tp'.groupdata) and
		getAllDataOfAnonUsersGroup[d4h, aug] in tp'.groupdata.AnonUsersGroup)
}

-- CHECKS and RUN

check sendUserDataOkay for 10
check sendGroupDataOkay for 10

run show for 4 but exactly 4 User, 4 Data, 1 ThirdParty, 2 Service, 1 AnonUsersGroup,
	3 HealthData, 3 Position






