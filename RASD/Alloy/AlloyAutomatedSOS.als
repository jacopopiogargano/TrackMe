-- SIGNATURES

sig Individual {}

sig HealthData {
	timestamp: one Int,
	heartRate: one HeartRate,
	data: one Data
}{timestamp>0}

sig HeartRate{
	value: one Int
}{value >=0}

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

one sig Data4Help{
	userdata: Data one -> one User
}

sig Service{
	users: set User,
	subscribedUsers: set User
}{subscribedUsers in users}

one sig AutomatedSOS extends Service{
	heartRateLowerThreshold: one Int,
	heartRateUpperThreshold: one Int,
	usersInNeed: set UserInNeed,
	userInNeedHandling: UserInNeed -> one LocalEmergencyServices
}{ heartRateLowerThreshold = 3 and heartRateUpperThreshold = 6 
	and subscribedUsers = users
	and (userInNeedHandling.LocalEmergencyServices) = usersInNeed}
-- { heartRateLowerThreshold = 40 and heartRateUpperThreshold = 200}

sig LocalEmergencyServices{
	usersInNeed: set UserInNeed
}

sig UserInNeed{
	user: one User
}

-- FUNCTIONS

fun retrieveUserData[d4h: Data4Help, u: User] : set Data {
	d4h.userdata.u
}

-- FACTS

fact userIndividualRelationshipIsUnique{
	all disj u1, u2:User, i:Individual |
	not (u1.individual = i and u2.individual = i)
}

fact userUserInNeedRelationshipIsUnique{
	all disj uin1, uin2: UserInNeed, u: User |
	not (uin1.user = u and uin2.user = u)
}

fact healthDataToDataConnection{
	all d:Data, hd: HealthData | 
	hd in d.healthData iff hd.data = d
}

fact postionToDataConnection{
	all d:Data, p: Position | 
	p in d.positions iff p.data = d
}

fact allHealthDataBelongsToOnlyOneData{
	all hd: HealthData | all disj d1,d2: Data |
	not (hd in d1.healthData and hd in d2.healthData)
}

fact allPositionBelongsToOnlyOneData{
	all p:Position | all disj d1,d2: Data |
	not (p in d1.positions and p in d2.positions)
}

fact userInNeedDefinition{
	all uin: UserInNeed, asos: AutomatedSOS, d4h: Data4Help| some hr: HeartRate |
	((hr.value < asos.heartRateLowerThreshold or hr.value > asos.heartRateUpperThreshold) 
	and hr in retrieveUserData[d4h, uin.user].healthData.heartRate)
	iff 
	(uin.user in asos.subscribedUsers and uin in asos.usersInNeed)
}

fact ifUserInNeedIsAssignedToLocalEmergencyServicesTheyAreLocalEmergencServicesUsersInNeed{
	all uin: UserInNeed, asos: AutomatedSOS, les: LocalEmergencyServices |
	uin in asos.userInNeedHandling.les iff uin in les.usersInNeed
}

pred show {}

-- RUN

run show for 3 but exactly 3 User, 2 HeartRate, 0 Service, 1 UserInNeed, 1 LocalEmergencyServices
