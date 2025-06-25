open util/boolean


sig User{
	files : some File,  //files inteira
	userEnc : Block -> EncBlock
}


sig File{
	blocks : some Block, //blocks inteiro
	var active:one Bool,  //indica qual file esta a ser escrito / eliminado
	var written:one Bool  //indica se um file ja foi escrito ou nao
} 


sig Block{
	hash : one Hash, // hash simples, inteira
}


sig EncBlock{
	var cleanDone : one Bool,  // indica se um bloco de um ficheiro a ser eliminado já foi eliminado
	var done : one Bool,	     // indica se um bloco de um ficheiro a ser enviado, já foi enviado	  
	decrypt: User -> Block
}

sig Hash{
	var index : Paddr -> Int
}

sig Paddr in Int{
	var freeBlock : one Bool   // indica se um paddr (endereço físico) encontra-se livre ou não
}



fact{
	all f:File | some u:User | u->f in files 	 // files sobrejetiva	
	files.~files in iden 					 // files injetiva

	all b:Block | some f:File | f->b in blocks // blocks sobrejetiva	

	hash.~hash in iden // hash injetiva  


	all u:User | all b:Block | some e:EncBlock | u->b->e in userEnc // userenc  inteiro
	all u:User | all b:Block | lone e:EncBlock | u->b->e in userEnc // userenc simples


	all u,u2:User | all b,b2:Block | all e,e2:EncBlock | (u->b->e in userEnc and u != u2 and u2->b2->e2 in userEnc) implies e != e2
	// para quaisquer dois users, a encriptação de um bloco é sempre diferente, independentemente se for o mesmo bloco ou não

	all e:EncBlock| all u:User | lone b:Block | e->u->b in decrypt; // decrypt simples
	all b:Block | some e:EncBlock | some u:User | e->u->b in decrypt // decrypt sobrejetiva

	all u:User | all b,b2:Block | all e:EncBlock | (e->u->b in decrypt and e->u->b2 in decrypt) implies b=b2

}




fact{
	always{
		all h:Hash | all p1,p2:Paddr | all n1,n2:Int | (h->p1->n1 in index and h->p2->n2 in index) implies (p1=p2 and n1=n2); // index simples
		// uma hash esta mapeada no máximo num paddr e num nref
	
		all h1,h2:Hash | all p:Paddr | all n:Int | (h1->p->n in index and h2->p->n in index) implies (h1=h2); //index injetiva
		// se duas hashes sao mapeadas no mesmo paddr, então são a mesma hash

		all p:Paddr | p < 0


		no True & (EncBlock.done & EncBlock.cleanDone)
		// ou blocos estão a ser escritos ou blocos estao a ser eliminados ou nada esta a ser escrito e eliminado
		// não podem existir blocos a serem escritos enquanto blocos tambem são eliminados
		
	}
}






fact{
	not True in EncBlock.done  //nenhum bloco está a ser escrito no inicio da simulaçao

	not True in EncBlock.cleanDone //nenhum bloco esta a ser eliminado no inicio da simulaçao

	no index	// index é relação vazia no inicio da simulação

	freeBlock = Paddr->True	// todos os paddrs se encontram livres no inicio da simulação

	written=File->False // nenhum ficheiro foi escrito no inicio da simulação

	active=File->False	// nenhum ficheiro esta a ser escrito ou eliminado no inicio da simulação
}




fact {
	#Block <= #EncBlock
	#Hash = #Paddr
	#Hash = #Block
}



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

pred send_block[e:EncBlock,u:User,f:File]{	 // se o bloco a enviar é original

	f->True in active 						// ficheiro está ativo
	not e->True in done 					//bloco ainda não foi escrito
	f->e.decrypt[u] in blocks					
//	f->bl in blocks and u->bl->e in userEnc 	//bloco pertence ao ficheiro, e enc é a encriptação correta do bloco com o user
	u->f in files							// o ficheiro pertence ao user
	no e.decrypt[u].hash.index              				// a hash do bloco não esta mapeada em index
	some True.~freeBlock					// existe um paddr livre para ser alocado


	active'=active
	written'=written
	cleanDone'=cleanDone
	index'=index+(e.decrypt[u].hash->min[True.~freeBlock]->1)                           	  //obtemos um paddr livre e mapeamos este em conjunto com nref=1 com a hash do bloco em index
	freeBlock'=(freeBlock-min[True.~freeBlock]->True)+(min[True.~freeBlock]->False)  //o paddr usado não se encontra mais livre	
	done'=(done-e->False)+e->True								  //o bloco foi enviado
}



pred send_block_dedup[e:EncBlock,u:User,f:File]{	   //se o bloco a enviar é duplicado

	f->True in active						// ficheiro está ativo
	not e->True in done					//bloco ainda não foi escrito
	f->e.decrypt[u] in blocks
//	f->bl in blocks and u->bl->e in userEnc    	//bloco pertence ao ficheiro, e enc é a encriptação correta do bloco com o    
	u->f in files							//o ficheiro pertence ao user
   	some e.decrypt[u].hash.index						// a hash do bloco ja se encontra mapeada num paddr e nref


	active'=active
	written'=written
	cleanDone'=cleanDone
	freeBlock'=freeBlock                               
	index'=(index-(e.decrypt[u].hash->Paddr->Int)) + (e.decrypt[u].hash->get_paddr[e.decrypt[u].hash,index]->(next[get_nref[e.decrypt[u].hash,index]]))  //incrementamos o nref associado à hash do bloco no index
	done'=(done-e->False)+e->True															     //o bloco foi enviado
}



fun get_paddr [h:Hash, s:Hash->Paddr->Int] : one Paddr{    //função que retorna o paddr associado a uma hash numa relação hash->paddr->int
	{p:Paddr| some n:Int | p->n in (h.s)}
}

fun get_nref[h:Hash, s:Hash->Paddr->Int]: one Int { //funçao que retorna o nref associado a uma hash numa relação hash->paddr->int
	{n:Int| some p:Paddr | p->n in (h.s)}
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

pred elim_block[e:EncBlock,u:User,f:File]{	                        // quando o bloco a ser eliminado tem a hash associada a um nref>1

	f->True in active										// ficheiro está ativo
	not e->True in cleanDone								// bloco não foi eliminado
	f->e.decrypt[u] in blocks
//	f->bl in blocks and u->bl->e in userEnc						// bloco pertence ao ficheiro e a encriptação está associada ao bloco e user
	u->f in files											// ficheiro pertence ao user
	some p:Paddr | some n:Int | e.decrypt[u].hash->p->n in index and n>1     // hash do bloco associado a nref>1

	active'=active
	written'=written	
	done'=done
	freeBlock'=freeBlock                            
	index'=(index-(e.decrypt[u].hash->Paddr->Int)) + (e.decrypt[u].hash->get_paddr[e.decrypt[u].hash,index]->(prev[get_nref[e.decrypt[u].hash,index]]))  // decrementamos o nref associado à hash do bloco no index
	cleanDone'=(cleanDone-e->False)+e->True													      // bloco foi eliminado

}



pred elim_block_clean[e:EncBlock,u:User,f:File]{		      	// quando o bloco a ser eliminado tem a hash associada a um nref>1

	f->True in active										// ficheiro está ativo
	not e->True in cleanDone								// bloco não foi eliminado
	f->e.decrypt[u] in blocks
//	f->bl in blocks and u->bl->e in userEnc						// bloco pertence ao ficheiro e a encriptação está associada ao bloco e user
	u->f in files											// ficheiro pertence ao user
	some p:Paddr | e.decrypt[u].hash->p->1 in index						// hash do bloco associado a nref=1

	active'=active
	written'=written	
	done'=done
	freeBlock'=(freeBlock- get_paddr[e.decrypt[u].hash,index]->False)+get_paddr[e.decrypt[u].hash,index]->True		// paddr associado à hash do bloco no index passa a estar livre    
	index'=index-(e.decrypt[u].hash->Paddr->Int)												// hash do bloco deixa de estar associada no index
	cleanDone'=(cleanDone-e->False)+e->True											// bloco foi eliminado

}


pred clean_done{         	// quando todos os blocos de um ficheiro foram enviado                         

	some u:User |some f:File | all bl:f.blocks | some enc:EncBlock | u->f in files and u->bl->enc in userEnc and enc.done=True and f->True in active 
	// existe um user com um ficheiro ativo, tal que todas as encriptações dos blocos desse ficheiro foram enviadas
	
	written'=(written- True.~active->False)+  True.~active->True    // ficheiro que se encontra ativo passa a estar escrito
	active'=File->False									     // nenhum ficheiro se encontra ativo
	index'=index   
	freeBlock'=freeBlock       	
	done'=EncBlock->False								     // nenhum bloco encriptado passa a estar enviado
	cleanDone'=cleanDone
}


pred clean_cleanDone{	// quando todos os blocos de um ficheiro foram eliminados

	some u:User |some f:File | all bl:f.blocks | some enc:EncBlock |u->f in files and u->bl->enc in userEnc and enc.cleanDone=True and f->True in active
	// existe um user com um ficheiro ativo, tal que todas as encriptações dos blocos desse ficheiro foram eliminadas	
	

	written'=(written- True.~active->True)+ 	True.~active->False	// ficheiro que se encontra ativo passa a não estar escrito
	active'=File->False										// nenhum ficheiro se encontra ativo
	index'=index   
	freeBlock'=freeBlock       	
	cleanDone'=EncBlock->False								// nenhum bloco encriptadao passa a estar eliminado
	done'=done
}



fact behavior{
	always{
		(some f:File | some u:User | send_file[u,f])
		or
		(some f:File | some u:User | elim_file[u,f])
		or
		(some e:EncBlock |some u:User| some f:File | send_block[e,u,f])
		or
		(some e:EncBlock |some u:User| some f:File | send_block_dedup[e,u,f])
		or
		(some e:EncBlock |some u:User| some f:File | elim_block[e,u,f])
		or
		(some e:EncBlock |some u:User| some f:File | elim_block_clean[e,u,f])
		or
		clean_done
		or
		clean_cleanDone
		or
		stutter
	}
}



run S0{
	some e1:EncBlock|some u:User| some f:File { send_file[u,f];send_block[e1,u,f];
                                                                clean_done }
} expect 1

run S1{   //teste tem que falhar: um user escreve 2 vezes o mesmo ficheiro
	some e1:EncBlock|some u:User| some f:File {  send_file[u,f];send_block[e1,u,f];
                                                                clean_done; send_block_dedup[e1,u,f]}
} expect 0 

run S2 {
	some u2,u1:User | some f1, f2: File |  some e1,e2,e3: EncBlock
        { send_file[u2,f1]; send_block[e2,u2,f1]; clean_done; send_file[u1,f2]; send_block_dedup[e3,u1,f2]; send_block[e1,u1,f2] }
} expect 1

				
run S3 {
	some u1:User | some f1: File |  some e1: EncBlock
        {  send_file[u1,f1 ];send_block[e1,u1,f1]; clean_done; elim_file[u1,f1]; elim_block_clean[e1,u1,f1] }
} expect 1

				
run S4 {
	some u2,u1:User | some f1, f2: File |  some e1,e2,e3: EncBlock
        {  send_file[u2,f1];send_block[e2,u2,f1]; clean_done;  send_file[u1,f2]; send_block_dedup[e3,u1,f2]; send_block[e1,u1,f2]; clean_done; elim_file[u2,f1]; elim_block[e2,u2,f1] }
} expect 1


run Sfail {
	some e1:EncBlock |some u:User| some f:File { send_file[u,f];send_block[e1,u,f];
                                                                clean_done;send_file[u,f];send_block[e1,u,f] }
} expect 0


run Sfail2enc{
	some e1,e2:EncBlock |some disj u1,u2:User| some f1,f2:File { send_file[u1,f1];send_block[e1,u1,f1];
                                                                clean_done;elim_file[u2,f2];elim_block_clean[e2,u2,f2] }
} expect 0







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
	(always no True.~written)
}