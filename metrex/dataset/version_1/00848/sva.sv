// Place inside cpu_write_controller or bind to it. Focused, concise SVA.

`ifdef ASSERT_ON
default clocking cb @(posedge mem_clk); endclocking
default disable iff (!hreset_n)

// Reset and state sanity
assert property (!hreset_n |-> current_state == cpuwr_state0);
assert property ($onehot({ current_state==cpuwr_state0,
                           current_state==cpuwr_state1,
                           current_state==cpuwr_state2,
                           current_state==cpuwr_state3,
                           current_state==cpuwr_state4 }));

// Next-state transitions
assert property (current_state==cpuwr_state0 &&  ff_wr_pend |=> current_state==cpuwr_state1);
assert property (current_state==cpuwr_state0 && !ff_wr_pend |=> current_state==cpuwr_state0);

assert property (current_state==cpuwr_state1 &&  cpu_wr_gnt |=> current_state==cpuwr_state2);
assert property (current_state==cpuwr_state1 && !cpu_wr_gnt |=> current_state==cpuwr_state1);

assert property (current_state==cpuwr_state2 &&  svga_ack |=> current_state==cpuwr_state3);
assert property (current_state==cpuwr_state2 && !svga_ack |=> current_state==cpuwr_state2);

assert property (current_state==cpuwr_state3 |=> current_state==cpuwr_state4);

// t32/t34 consistency and state4 exits
assert property (! $isunknown({ff_wr_pend,crt_req}) |-> (t34 == ~t32));
assert property (current_state==cpuwr_state4 &&  t34 && !t32 |=> current_state==cpuwr_state0);
assert property (current_state==cpuwr_state4 &&  t32 && !t34 |=> current_state==cpuwr_state2);
// If inputs are known, we must not hold in state4
assert property (current_state==cpuwr_state4 && ! $isunknown({ff_wr_pend,crt_req}) |=> current_state != cpuwr_state4);

// Output/function equivalences
assert property (cpu_mem_wr == cpu_wr_req);
assert property (cpu_fifo_read == enwr_cpu_ad_da_pl);
assert property (enwr_cpu_ad_da_pl == (ff_wr_pend & en_cpu_fifo_read));
assert property (cpu_wr_svga_req == (int_cpu_wr_svga_req & ff_wr_pend));

assert property (cpu_wr_req == (current_state != cpuwr_state0));
assert property (cpu_arb_wr == (current_state inside {cpuwr_state2,cpuwr_state3,cpuwr_state4}));
assert property (int_cpu_fifo_rd == (current_state == cpuwr_state2));
assert property (int_cpu_wr_svga_req == (current_state == cpuwr_state2));
assert property (en_cpu_fifo_read == (current_state == cpuwr_state3));
assert property (cpu_arb_wr |-> cpu_wr_req);

// No-X on key signals when inputs known
assert property (! $isunknown({ff_wr_pend,crt_req,cpu_wr_gnt,svga_ack}) |->
                 ! $isunknown({current_state,cpu_wr_req,cpu_arb_wr,int_cpu_fifo_rd,
                               int_cpu_wr_svga_req,en_cpu_fifo_read,cpu_wr_svga_req,
                               cpu_fifo_read,enwr_cpu_ad_da_pl,cpu_mem_wr,t32,t34}));

// Coverage: full successful write and both state4 exits
cover property (current_state==cpuwr_state0 && ff_wr_pend
                ##1 current_state==cpuwr_state1
                ##1 cpu_wr_gnt && current_state==cpuwr_state1
                ##1 current_state==cpuwr_state2
                ##1 svga_ack   && current_state==cpuwr_state2
                ##1 current_state==cpuwr_state3
                ##1 current_state==cpuwr_state4
                ##1 t34 && !t32
                ##1 current_state==cpuwr_state0);

cover property (current_state==cpuwr_state4 && t32 && !t34 ##1 current_state==cpuwr_state2);
cover property (current_state==cpuwr_state3 && ff_wr_pend && en_cpu_fifo_read && cpu_fifo_read);
cover property (current_state==cpuwr_state2 && ff_wr_pend && int_cpu_wr_svga_req && cpu_wr_svga_req);

`endif