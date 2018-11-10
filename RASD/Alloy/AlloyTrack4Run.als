--------------------------------------------------------- SIGNATURES -------------------------------------------------

sig Individual {}

sig User {
	individual: one Individual
}

sig Participant {
	user: one User
}

sig Spectator {
	individual: one Individual
}

sig Organizer {
	individual: one Individual
}

sig Data{}

sig Position{
	lat: one Int,
	long: one Int
}

one sig Data4Help{
	userdata: Data one -> one User
}

sig Service{
	-- users who gave consent to their data acquisition by the service
	users: set User,
	subscribedUsers: set User
}{subscribedUsers in users}

one sig Track4Run extends Service {
	organizerRun: Organizer one -> RunningCompetition,
	participantRun: Participant -> one RunningCompetition,
	spectatorRun: Spectator -> one RunningCompetition
} {(participantRun.RunningCompetition).user in subscribedUsers}

sig RunningCompetition {
	start: one Position,
	end: one Position,
	maxNumberOfParticipants: one Int
}

--------------------------------------------------FUNCTIONS----------------------------------------------------
fun getRunningCompetitionForParticipant[t4r: Track4Run, p:Participant] : RunningCompetition {
	(t4r.participantRun)[p]
}

fun getRunningCompetitionForSpectator[t4r: Track4Run, s:Spectator] : RunningCompetition {
	(t4r.spectatorRun)[s]
}

fun getNumberOfParticipantsForRunningCompetition[t4r: Track4Run, r: RunningCompetition] : Int {
	#(t4r.participantRun.r)
} 

--------------------------------------------------- FACTS -------------------------------------------------------
fact userIndividualRelationshipIsUnique{
	all disj u1, u2:User, i:Individual | not (u1.individual = i and u2.individual = i)
}

fact organizerIndividualRelationshipIsUnique{
	all disj o1, o2:Organizer, i:Individual | not (o1.individual = i and o2.individual = i)
}

-- this implies also that user cannot re-enroll in a running competition they are already participants of
fact userCantAppearTwiceInRunningCompetition{
	all disj p1, p2:Participant, t4r:Track4Run |
	p1.user = p2.user implies getRunningCompetitionForParticipant[t4r, p1] != getRunningCompetitionForParticipant[t4r, p2]
}

fact individualCantAppearTwiceAsSpectatorOfRunningCompetition{
	all disj s1, s2:Spectator, t4r:Track4Run |
	s1.individual = s2.individual implies getRunningCompetitionForSpectator[t4r, s1] != getRunningCompetitionForSpectator[t4r, s2]
}

fact limitParticipantsToMaxNumberOfParticipants{
	all r:RunningCompetition, t4r:Track4Run |
	getNumberOfParticipantsForRunningCompetition[t4r, r] <= r.maxNumberOfParticipants
}

fact participantCannotBeSpectator{
	all p:Participant, s:Spectator,t4r:Track4Run |
	p.user.individual = s.individual implies getRunningCompetitionForParticipant[t4r,p] != getRunningCompetitionForSpectator[t4r,s]
}

----------------------------------------------- PREDICATES -------------------------------------------------------
pred userEnrollsInRunningCompetition[p:Participant, u:User, t4r,t4r':Track4Run, r:RunningCompetition] {
	u in t4r.users
	getNumberOfParticipantsForRunningCompetition[t4r, r] < r.maxNumberOfParticipants
	p.user = u
	t4r'.participantRun = t4r.participantRun + p->r
}

/*
pred checkNumberOfParticipantsAfterEnrollment [r:RunningCompetition, t4r:Track4Run] {
	o->r in t4r.organizerRun
	
}
*/

pred show{}
----------------------------------------------- ASSERTIONS -------------------------------------------------------
assert userCanEnrollWhenNumberOfParticipantsIsNotMax{
	all u: User, t4r, t4r':Track4Run, p:Participant, r:RunningCompetition |
	p->r not in t4r.participantRun and userEnrollsInRunningCompetition[p,u,t4r, t4r',r] implies p->r in t4r'.participantRun
}

----------------------------------------------- CHECKS and RUNS -------------------------------------------------------
check userCanEnrollWhenNumberOfParticipantsIsNotMax for 10
run show for 4 but exactly 0 Service, 2 Participant, 2 Data




