sig Password {}
sig User {
	var password : set Password
}
var sig LoggedIn in User {}

// Guess what is the behavior of this authentication concept!
// To check how many points you have so far you can use the different commands. 
// The maximum is 5 points.


pred stutter{
	LoggedIn' = LoggedIn
	password' = password
}


pred createAccount[u : User]{
  	// guard
  	no u.password and u not in LoggedIn
    // effect
  	some pwd: Password | password' = password + u->pwd
    // frame condition
  	LoggedIn' = LoggedIn
}


pred login[u : User, pwd : Password]{
  	// guards
	u not in LoggedIn
  	one u.password and u->pwd in password
  	// effect
	LoggedIn' = LoggedIn + u
  	// frame condition
  	password' = password
}


pred changePassword[u : User, newPwd : Password]{
	// guards 
	historically u->newPwd not in password
	u in LoggedIn
  	one u.password
	// effect
 	all oldPwd: u.password | password' = password - u->oldPwd + u->newPwd
  	// frame condition
	LoggedIn' = LoggedIn
}


pred logout[u : User]{
	// guard
	u in LoggedIn
  	// effect
  	LoggedIn' = LoggedIn - u
  	// frame condition
 	password' = password
}


pred deleteAccount[u : User]{
  	// guard
	u in LoggedIn
  	// effect
  	LoggedIn' = LoggedIn - u
  	// frame condition
  	no password'
}


fact Proprieties{
  
  	// Criar conta só será verdadeira até apagar conta.
  	all u: User | always (createAccount[u] until deleteAccount[u])
  
  	// Fazer login implica que a conta já tenha sido registada uma vez e, também, só é verdadeiro até fazer logout.
	all u: User | all pwd: u.password | always ((login[u,pwd] implies once createAccount[u]) and (login[u,pwd] until logout[u]))
  
  	// Fazer logout implica que o login já tenha sido feito e o logout torna falso o login.
  	all u: User | all pwd: u.password | always ((logout[u] implies once login[u,pwd]) and (logout[u] releases login[u,pwd]))
  
  	// Apagar conta implica que a conta já tenha sido registada e torna falso criar conta.
  	all u: User | always ((deleteAccount[u] implies once createAccount[u]) and (deleteAccount[u] releases createAccount[u]))
  
  	// Mudar de password implica que o login já tenha sido feito.
  	all u: User | all pwd: u.password | some newPwd: Password - pwd | always (changePassword[u,newPwd] implies once login[u,pwd])
  
}


pred behavior {

	no password
	no LoggedIn
  	
  	always{
      (some u: User, pwd: Password |
      		createAccount[u]
      		or login[u,pwd]
            or changePassword[u,pwd]
            or logout[u]
      		or deleteAccount[u]
  	  ) or stutter
  	}
}