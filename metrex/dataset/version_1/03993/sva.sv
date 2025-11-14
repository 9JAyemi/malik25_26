// SVA checker for dual_port_mem
// Bind this module to the DUT:
//   bind dual_port_mem dual_port_mem_sva #(.DATA_WIDTH(`DATA_WIDTH)) u_dual_port_mem_sva (.*);

module dual_port_mem_sva #(parameter int DATA_WIDTH = 32) (
  input clk,
  input r_en1,
  input [1:0] r_addr1,
  input r_en2,
  input [1:0] r_addr2,
  input w_en,
  input [1:0] w_addr,
  input [2*(DATA_WIDTH+1)-1:0] w_data,
  input [2*(DATA_WIDTH+1)-1:0] r_data1,
  input [2*(DATA_WIDTH+1)-1:0] r_data2
);
  localparam int DW = 2*(DATA_WIDTH+1);

  default clocking @(posedge clk); endclocking

  // Shadow memory model (mirrors DUT mem after writes each cycle)
  logic [DW-1:0] ref_mem [0:3];
  logic init1, init2;  // warm-up for $past
  always_ff @(posedge clk) begin
    init1 <= 1'b1;
    init2 <= init1;
    if (w_en) ref_mem[w_addr] <= w_data;
  end

  // Control must be known (after first edge)
  assert property (disable iff (!init1) !$isunknown({r_en1,r_en2,w_en,r_addr1,r_addr2,w_addr}))
    else $error("dual_port_mem: X/Z on controls or addresses");

  // Both reads: read-before-write semantics
  assert property (disable iff (!init2)
                   (r_en1 && r_en2) |->
                   (r_data1 == $past(ref_mem[r_addr1]) &&
                    r_data2 == $past(ref_mem[r_addr2])))
    else $error("dual_port_mem: both-read data mismatch");

  // Single read on port1; port2 forced to zero
  assert property (disable iff (!init2)
                   (r_en1 && !r_en2) |->
                   (r_data1 == $past(ref_mem[r_addr1]) && r_data2 == '0))
    else $error("dual_port_mem: port1 read or port2 zero mismatch");

  // Single read on port2; port1 forced to zero
  assert property (disable iff (!init2)
                   (!r_en1 && r_en2) |->
                   (r_data1 == '0 && r_data2 == $past(ref_mem[r_addr2])))
    else $error("dual_port_mem: port2 read or port1 zero mismatch");

  // No reads: outputs hold value
  assert property (disable iff (!init2)
                   (!r_en1 && !r_en2) |->
                   (r_data1 == $past(r_data1) && r_data2 == $past(r_data2)))
    else $error("dual_port_mem: outputs should hold when no read");

  // Both ports read same address => identical data (old mem value)
  assert property (disable iff (!init2)
                   (r_en1 && r_en2 && (r_addr1 == r_addr2)) |->
                   (r_data1 == r_data2 && r_data1 == $past(ref_mem[r_addr1])))
    else $error("dual_port_mem: same-address dual read mismatch");

  // Functional coverage
  cover property (r_en1 && !r_en2);
  cover property (!r_en1 && r_en2);
  cover property (r_en1 && r_en2 && (r_addr1 != r_addr2));
  cover property (r_en1 && r_en2 && (r_addr1 == r_addr2));
  cover property (w_en);
  cover property (w_en ##1 (r_en1 && (r_addr1 == $past(w_addr)))); // RAW on port1
  cover property (w_en ##1 (r_en2 && (r_addr2 == $past(w_addr)))); // RAW on port2
  cover property (w_en && r_en1 && (w_addr == r_addr1));           // same-cycle W+R1 (read old)
  cover property (w_en && r_en2 && (w_addr == r_addr2));           // same-cycle W+R2 (read old)
  cover property (!r_en1 && !r_en2);                               // hold cycle
endmodule