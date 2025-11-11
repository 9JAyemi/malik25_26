// SVA for addr_gen and its counters. Concise, high-signal-coverage, focused on behavior.
// Bind these into your simulation/formal environment.

bind addr_gen addr_gen_sva sva_addr_gen (.*);

module addr_gen_sva(
  input logic nrst, clk,
  input logic wr_en, wr_inc, load_w2r, rd_inc,
  input logic [7:0]  rd_step,
  input logic [17:0] addr_wr, addr_rd,
  input logic        wr_end
);
  // Expected signed extension of rd_step to 18 bits (reference model)
  logic [17:0] rd_step_ex_ref;
  assign rd_step_ex_ref = {{10{rd_step[7]}}, rd_step};

  // Reset values
  assert property (@(posedge clk) !nrst |-> (addr_wr==18'b0 && addr_rd==18'b0 && wr_end==1'b0));

  // Write counter behavior (en = wr_en & wr_inc & ~wr_end; step=1; load=0)
  assert property (@(posedge clk) disable iff(!nrst)
                   ( wr_en &&  wr_inc && !wr_end) |=> addr_wr == $past(addr_wr) + 18'd1);
  assert property (@(posedge clk) disable iff(!nrst)
                   (!wr_en || !wr_inc ||  wr_end) |=> addr_wr == $past(addr_wr));

  // Read counter behavior
  // load has precedence over en, and loads addr_wr
  assert property (@(posedge clk) disable iff(!nrst)
                   load_w2r |=> addr_rd == $past(addr_wr));
  // When not loading, increment/decrement by signed-extended step
  assert property (@(posedge clk) disable iff(!nrst)
                   (!load_w2r && rd_inc) |=> addr_rd == $past(addr_rd) + $past(rd_step_ex_ref));
  // Hold when neither load nor en
  assert property (@(posedge clk) disable iff(!nrst)
                   (!load_w2r && !rd_inc) |=> addr_rd == $past(addr_rd));

  // wr_end control
  // Set when write and read addresses reach equality (reach)
  assert property (@(posedge clk) disable iff(!nrst)
                   (addr_wr == addr_rd) |=> wr_end);
  // A fall of wr_end happens only because wr_en deasserted (not during reset)
  assert property (@(posedge clk) disable iff(!nrst)
                   $fell(wr_end) |-> !wr_en);
  // Rising wr_end implies reach was true in the previous cycle
  assert property (@(posedge clk) disable iff(!nrst)
                   $rose(wr_end) |-> $past(addr_wr == addr_rd));
  // Sticky while wr_en remains high
  assert property (@(posedge clk) disable iff(!nrst)
                   (wr_end && wr_en) |=> wr_end);
  // If not reaching and wr_en is low, wr_end clears
  assert property (@(posedge clk) disable iff(!nrst)
                   (!wr_en && (addr_wr != addr_rd)) |=> !wr_end);

  // Functional coverage (key scenarios)
  cover property (@(posedge clk) disable iff(!nrst) 1'b1 ##[1:$] wr_end);                   // eventually reach
  cover property (@(posedge clk) disable iff(!nrst) load_w2r);                               // load rd from wr
  cover property (@(posedge clk) disable iff(!nrst) rd_inc &&  rd_step[7]);                  // negative step used
  cover property (@(posedge clk) disable iff(!nrst) rd_inc && (rd_step==8'h00));             // zero step (hold)
  cover property (@(posedge clk) disable iff(!nrst) wr_end && wr_en && wr_inc ##1
                                        addr_wr == $past(addr_wr));                          // wr gated by wr_end
endmodule


// Optional: generic counter SVA bound to all cnt instances
bind cnt cnt_sva #(.WIDTH(WIDTH)) sva_cnt (.*);

module cnt_sva #(parameter WIDTH=8)(
  input logic nrst, clk,
  input logic en, load,
  input logic [WIDTH-1:0] step, cin,
  input logic [WIDTH-1:0] cnt
);
  // Reset to zero
  assert property (@(posedge clk) !nrst |-> cnt=={WIDTH{1'b0}});
  // Load has precedence and uses cin sampled in previous cycle
  assert property (@(posedge clk) disable iff(!nrst) load |=> cnt == $past(cin));
  // Increment when enabled and not loading
  assert property (@(posedge clk) disable iff(!nrst) (!load && en) |=> cnt == $past(cnt) + $past(step));
  // Hold when idle
  assert property (@(posedge clk) disable iff(!nrst) (!load && !en) |=> cnt == $past(cnt));
endmodule