all: ticket.out ticket_nested.out alternating_bit_protocol.out hybrid_reliable_broadcast_cisa.out tlb.out

%.out: %.ivy
	ivy_check $< > $@

clean:
	rm -vf *.out
