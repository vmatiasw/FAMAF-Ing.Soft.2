sig Addr, Data {}

sig Memory { 
 	addrs: Addr,
	map: addrs -> one Data
}

sig Cache extends Memory { dirty: set addrs }{}

pred Write [m,mˋ: Memory, d: Data, a: Addr] {
 	mˋ.map = m.map ++ (a -> d)
	and mˋ.addrs = m.addrs
}

pred CacheWrite[m,mˋ: Cache, d: Data, a: Addr] {
	Write[m, mˋ, d, a]
	and mˋ.dirty = m.dirty + a
}

pred Load[s,sˋ: System, a: Addr]{
	Write[s.cache, sˋ.cache, s.main.map[a], a]
	and sˋ.cache.dirty = s.cache.dirty - a
	and sˋ.main = s.main
}

pred Flush[s,sˋ: System]{
	all a : Addr | 
		a in s.cache.dirty 
		implies Write[s.main,sˋ.main,s.cache.map[a],a]
	and no sˋ.cache.dirty
}

sig MainMemory extends Memory { }

sig System {
 cache: Cache,
 main: MainMemory
 }

pred Consistent [s:System] {
	s.cache.map - (s.cache.dirty -> Data) in s.main.map
}

assert WriteConsistent {
	all s,sˋ,sˋˋ:System, d:Data, a:Addr | 
		Consistent[s] 
		and Write[s.main,sˋ.main,d,a]
		and Load[sˋ,sˋˋ,a] 
		implies Consistent[sˋˋ]
}
check WriteConsistent for 6 but 3 System

assert CacheWriteConsistent {
	all s,sˋ:System, d:Data, a:Addr | 
		Consistent[s] 
		and CacheWrite[s.cache,sˋ.cache,d,a] 
		implies Consistent[sˋ]
}
check CacheWriteConsistent for 6 but 2 System

assert LoadConsistent {
	all s,sˋ:System, a:Addr | 
		Consistent[s] 
		and Load[s,sˋ,a] 
		implies Consistent[sˋ]
}
check LoadConsistent for 6 but 2 System

assert FlushConsistent {
	all s,sˋ:System | 
		Consistent[s] 
		and Flush[s,sˋ] 
		implies Consistent[sˋ]
}
check FlushConsistent for 6 but 2 System

