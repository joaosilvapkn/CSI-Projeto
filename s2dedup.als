open util/boolean

sig User{
	files : some File,  //files inteira
}


sig File{
	blocks : some Block, //blocks inteiro
	var active:one Bool,  //indica qual file esta a ser escrito / eliminado
	var written:one Bool  //indica se um file ja foi escrito ou nao
} 



sig Block{
	hash : one Hash, 			// hash simples e inteira   
	var cleanDone : one Bool,	// indica se um bloco de um ficheiro a ser eliminado, já foi eliminado
	var done : one Bool		// indica se um bloco de um ficheiro a ser enviado, já foi enviado

}

sig Hash{
	var index : Paddr->Int	
}



sig Paddr in Int{
	var freeBlock : one Bool		// indica se um paddr (endereço físico) encontra-se livre ou não

}






fact{
	all f:File | some u:User | u->f in files 	 // files sobrejetiva	
	files.~files in iden 					 // files injetiva

	all b:Block | some f:File | f->b in blocks // blocks sobrejetiva	

	hash.~hash in iden // hash injetiva  
}



fact{
	always{
		all h:Hash | all p1,p2:Paddr | all n1,n2:Int | (h->p1->n1 in index and h->p2->n2 in index) implies (p1=p2 and n1=n2); // index simples
		// uma hash esta mapeada no máximo num paddr e num nref
	
		all h1,h2:Hash | all p:Paddr | all n:Int | (h1->p->n in index and h2->p->n in index) implies (h1=h2); //index injetiva
		// se duas hashes sao mapeadas no mesmo paddr, então são a mesma hash

		all p:Paddr | p < 0


		no True & (Block.done & Block.cleanDone)
		// ou blocos estão a ser escritos ou blocos estao a ser eliminados ou nada esta a ser escrito e eliminado
		// não podem existir blocos a serem escritos enquanto blocos tambem são eliminados
		
	}
}


fact{
	not True in Block.done  //nenhum bloco está a ser escrito no inicio da simulaçao

	not True in Block.cleanDone //nenhum bloco esta a ser eliminado no inicio da simulaçao

	no index	// index é relação vazia no inicio da simulação

	freeBlock = Paddr->True	// todos os paddrs se encontram livres no inicio da simulação

	written=File->False // nenhum ficheiro foi escrito no inicio da simulação

	active=File->False	// nenhum ficheiro esta a ser escrito ou eliminado no inicio da simulação
}




fact {
	#Hash = #Paddr
	#Hash = #Block
}



fact{
	always{
	all h:Hash | all p1,p2:Paddr | all n1,n2:Int | (h->p1->n1 in index and h->p2->n2 in index) implies (p1=p2 and n1=n2); // index simples
	// uma hash esta mapeada no máximo num paddr e num nref

	all h1,h2:Hash | all p:Paddr | all n:Int | (h1->p->n in index and h2->p->n in index) implies (h1=h2) //index injetiva
	// se duas hashes sao mapeadas no mesmo paddr, então são a mesma hash

	all p:Paddr | p < 0
	}
}


fact{
	always{    
		no True & (Block.done & Block.cleanDone) // ou se recebem blocos de um ficheiro, ou se eliminam blocos de um ficheiro, nunca ambos
	}                                                                     
}


fact {
	#Hash = #Paddr
	#Hash = #Block
}



------------------------------------------------------------------------------------------------------------------



pred stutter{
	active'=active
	written'=written
	index'=index
	freeBlock'=freeBlock
	done'=done
	cleanDone'=cleanDone
}



pred send_file[u:User,f:File]{    // um ficheiro de um user vai ser escrito

	//pre condições
	active=File->False   //nenhum ficheiro se encontra ativo
	f->False in written	//o ficheiro ainda não foi escrito
	u->f in files		//o ficheiro pertence ao user em questão
	
	active'=(active-f->False)+f->True  // ficheiro torna-se ativo
	written'=written	
	index'=index
	freeBlock'=freeBlock
	done'=done
	cleanDone'=cleanDone
}





pred send_block[b:Block,u:User,f:File]{	 	// se o bloco a enviar é original

	f->True in active 						// ficheiro está ativo
	not b->True in done 					//bloco ainda não foi escrito
	f->b in blocks						 	//bloco pertence ao ficheiro
	u->f in files							// o ficheiro pertence ao user
	no b.hash.index              					// a hash do bloco não esta mapeada em index
	some True.~freeBlock					// existe um paddr livre para ser alocado



	active'=active
	written'=written
	cleanDone'=cleanDone
	index'=index+(b.hash->min[True.~freeBlock]->1)                           	  //obtemos um paddr livre e mapeamos este em conjunto com nref=1 com a hash do bloco em index
	freeBlock'=(freeBlock-min[True.~freeBlock]->True)+(min[True.~freeBlock]->False)  //o paddr usado não se encontra mais livre	
	done'=(done-b->False)+b->True								  //o bloco foi enviado
}




pred send_block_dedup[b:Block,u:User,f:File]{	 //se o bloco a enviar é duplicado

	f->True in active						// ficheiro está ativo
	not b->True in done					//bloco ainda não foi escrito
	f->b in blocks						    	//bloco pertence ao ficheiro
	u->f in files							//o ficheiro pertence ao user
   	some b.hash.index						// a hash do bloco ja se encontra mapeada num paddr e nref


	active'=active
	written'=written
	cleanDone'=cleanDone
	freeBlock'=freeBlock                               
	index'=(index-(b.hash->Paddr->Int)) + (b.hash->get_paddr[b.hash,index]->(next[get_nref[b.hash,index]]))  //incrementamos o nref associado à hash do bloco no index
	done'=(done-b->False)+b->True															   //o bloco foi enviado
}








fun get_paddr [h:Hash, s:Hash->Paddr->Int] : one Paddr{    //função que retorna o paddr associado a uma hash numa relação hash->paddr->int
	{p:Paddr| some n:Int | p->n in (h.s)}
}

fun get_nref[h:Hash, s:Hash->Paddr->Int]: one Int { 	   	  //funçao que retorna o nref associado a uma hash numa relação hash->paddr->int
	{n:Int| some p:Paddr | p->n in (h.s)}
}


pred clean_done{         	// quando todos os blocos de um ficheiro foram enviado

	some f:File | f.blocks.done=True and f.active=True	
	// existe um user com um ficheiro ativo, tal que todos os blocos desse ficheiro foram enviados

	written'=(written- True.~active->False)+  True.~active->True    // ficheiro que se encontra ativo passa a estar escrito
	active'=File->False									     // nenhum ficheiro se encontra ativo
	cleanDone'=cleanDone
	index'=index   
	freeBlock'=freeBlock       	
	done'=Block->False								    // nenhum bloco passa a estar enviado
	
}	

	



pred elim_file[u:User,f:File]{

	//pre condições
	active=File->False	//nenhum ficheiro se encontra ativo
	f->True in written	//o ficheiro já foi escrito	
	u->f in files		//o ficheiro pertence ao user
	
	active'=(active-f->False)+f->True	// ficheiro torna-se ativo
	written'=written
	index'=index
	freeBlock'=freeBlock
	done'=done
	cleanDone'=cleanDone
}




pred elim_block[b:Block,u:User,f:File]{	                        // quando o bloco a ser eliminado tem a hash associada a um nref>1

	f->True in active										// ficheiro está ativo
	not b->True in cleanDone								// bloco não foi eliminado
	f->b in blocks											// bloco pertence ao ficheiro
	u->f in files											// ficheiro pertence ao user
	some p:Paddr | some n:Int | b.hash->p->n in index and n>1     // hash do bloco associado a nref>1

	active'=active
	written'=written	
	done'=done
	freeBlock'=freeBlock                            
	index'=(index-(b.hash->Paddr->Int)) + (b.hash->get_paddr[b.hash,index]->(prev[get_nref[b.hash,index]]))  // decrementamos o nref associado à hash do bloco no index
	cleanDone'=(cleanDone-b->False)+b->True													   // bloco foi eliminado
}




pred elim_block_clean[b:Block,u:User,f:File]{				      	// quando o bloco a ser eliminado tem a hash associada a um nref>1

	f->True in active										// ficheiro está ativo
	not b->True in cleanDone								// bloco não foi eliminado
	f->b in blocks            									// bloco pertence ao ficheiro
	u->f in files											// ficheiro pertence ao user
	some p:Paddr | b.hash->p->1 in index						// hash do bloco associado a nref=1

	active'=active
	written'=written	
	done'=done
	freeBlock'=(freeBlock- get_paddr[b.hash,index]->False)+get_paddr[b.hash,index]->True		// paddr associado à hash do bloco no index passa a estar livre    
	index'=index-(b.hash->Paddr->Int)											          	// hash do bloco deixa de estar associada no index
	cleanDone'=(cleanDone-b->False)+b->True											// bloco foi eliminado

}


pred clean_cleanDone{	// quando todos os blocos de um ficheiro foram eliminados

	some f:File | f.blocks.cleanDone=True and f.active=True
	// existe um user com um ficheiro ativo, tal que todos blocos desse ficheiro foram eliminados	
	
	written'=(written- True.~active->True)+ 	True.~active->False	// ficheiro que se encontra ativo passa a não estar escrito
	active'=File->False										// nenhum ficheiro se encontra ativo
	index'=index   
	freeBlock'=freeBlock       	
	cleanDone'=Block->False								// nenhum bloco encriptadao passa a estar eliminado
	done'=done
}







fact behavior{
	always{
		(some f:File | some u:User | send_file[u,f])
		or
		(some f:File | some u:User | elim_file[u,f])
		or
		(some b:Block |some u:User| some f:File | send_block[b,u,f])
		or
		(some b:Block |some u:User| some f:File | send_block_dedup[b,u,f])
		or
		(some b:Block |some u:User| some f:File | elim_block[b,u,f])
		or
		(some b:Block |some u:User| some f:File | elim_block_clean[b,u,f])
		or
		clean_done
		or
		clean_cleanDone
		or
		stutter
	}
}





run S0{
	some b1:Block |some u:User| some f:File { send_file[u,f];send_block[b1,u,f];
                                                                clean_done }
}

run S1{		 //teste tem que falhar: um user escreve 2 vezes o mesmo ficheiro
	some b1:Block |some u:User| some f:File {  send_file[u,f];send_block[b1,u,f];
                                                                clean_done; send_file[u,f]; send_block_dedup[b1,u,f]}
} for 4 File, exactly 2 Block, exactly 2 Hash, 2 User


run S2 {
	some u2,u1:User | some f1, f2: File | some b1,b2: Block
        { send_file[u2,f1]; send_block[b2,u2,f1]; clean_done; send_file[u1,f2]; send_block_dedup[b2,u1,f2]; send_block[b1,u1,f2] }
}

			
run S3 {
	some u1:User | some f1: File | some b1: Block
        {  send_file[u1,f1 ];send_block[b1,u1,f1]; clean_done; elim_file[u1,f1]; elim_block_clean[b1,u1,f1] }
}


				
run S4 {
	some u2,u1:User | some f1, f2: File | some b1,b2: Block
        {  send_file[u2,f1];send_block[b2,u2,f1]; clean_done;  send_file[u1,f2]; send_block_dedup[b2,u1,f2]; send_block[b1,u1,f2]; clean_done; elim_file[u2,f1]; elim_block[b2,u2,f1] }
}



run Sfail {
	some b1:Block |some u:User| some f:File { send_file[u,f];send_block[b1,u,f];
                                                                clean_done;send_file[u,f];send_block[b1,u,f] }
}


run Sfail2{
	some b1:Block |some disj u1,u2:User| some f1,f2:File { send_file[u1,f1];send_block[b1,u1,f1];
                                                                clean_done;elim_file[u2,f2];elim_block_clean[b1,u2,f2] }
}






check OP1{	// se um user elimina um ficheiro, entao antes enviou o mesmo
	
	all f:File| all u:User | always {
		elim_file[u,f]
		implies
		once send_file[u,f]
	} 
}


check OP2{	// o primeiro evento a ocorrer será um send_file
	(always  stutter)
	or
	(some u:User,f:File | stutter until  send_file[u,f]) 
}

check OP3{  // se um ficheiro está escrito, apenas poderá não estar escrito depois de um cleandone
	
	all f:File | always{
		f->True in written
		implies
		(clean_cleanDone releases f->True in written)		
	}
}




check OP4{  // se nunca ocorre eliminação de ficheiros, os ficheiros escritos nunca diminuem
		
	(all u:User | all f:File | always {not elim_file[u,f]})
	implies
	(always True.~written in True.~written')
}


check OP5{  // se nunca se enviam ficheiros, os ficheiros não escritos nunca diminuem
		
	(all u:User | all f:File | always {not send_file[u,f]})
	implies
	(always False.~written in False.~written')
}
