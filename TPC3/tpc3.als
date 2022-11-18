sig Password {}
sig User {
	var password : set Password
}
var sig LoggedIn in User {}

// Guess what is the behavior of this authentication concept!
// To check how many points you have so far you can use the different commands. 
// The maximum is 5 points.

fact{
  	// Todos os usuários não logados podem ter ou não password (dependendo se estão ou não registados)
  	all u: User-LoggedIn | lone u.password
  	// Todos os usuários logados têm uma e só uma password
	all u: User | u in LoggedIn implies one u.password
}


pred stutter{
  	all u: User | u.password' = u.password
	LoggedIn' = LoggedIn
}


pred createAccount[u : User, pwd : Password]{
  	u->pwd not in password
 	historically u not in LoggedIn
  	password' = password + u->pwd
  	LoggedIn' = LoggedIn + u
}


pred deleteAccount[u : User, pwd : Password]{
  	u in LoggedIn and pwd in u.password
  	password' = password - u->pwd
  	LoggedIn' = LoggedIn - u
}


pred changePassword[u : User, newPwd : Password]{
  	u in LoggedIn
	historically u->newPwd not in password
  	password' = password - u->u.password + u->newPwd
	LoggedIn' = LoggedIn
}


pred login[u : User]{
	u not in LoggedIn and one u.password
	LoggedIn' = LoggedIn + u
  	password' = password
}


pred logout[u : User]{
	u in LoggedIn
  	LoggedIn' = LoggedIn - u
 	password' = password
}


pred behavior {

	no LoggedIn
	all u: User | no u.password
  
  	always{
	    (some u: User, pwd: Password |
      		createAccount[u,pwd]
            	or changePassword[u,pwd]
      		or deleteAccount[u,pwd]
      		or login[u]
            	or logout[u]
  	    ) or stutter
  	}
}
