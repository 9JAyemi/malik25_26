// SVA for blockmem2rptr1w
// Concise, high-quality checks and coverage
`ifndef SYNTHESIS
module blockmem2rptr1w_sva
(
  input  logic         clk,
  input  logic         reset_n,
  input  logic         rst,
  input  logic         cs,
  input  logic         wr,
  input  logic [7:0]   read_addr0,
  input  logic [7:0]   write_addr,
  input  logic [31:0]  write_data,
  input  logic [31:0]  read_data0,
  input  logic [31:0]  read_data1,

  // internal DUT signals
  input  logic [31:0]  tmp_read_data0,
  input  logic [7:0]   ptr_reg,
  input  logic [7:0]   ptr_new,
  input  logic         ptr_we,
  input  logic [31:0]  mem [0:255]
);

  // track availability of $past
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic input sanity
  assert property (@(posedge clk) !$isunknown({reset_n, rst, cs, wr, read_addr0, write_addr}));

  // Asynchronous reset behavior for ptr_reg (checked at clock edges)
  assert property (@(posedge clk) !reset_n |-> (ptr_reg == 8'h00));

  // Combinational ptr_logic invariants
  assert property (@(posedge clk) ptr_we  == (rst || cs));
  assert property (@(posedge clk) ptr_new == (cs ? (ptr_reg + 8'h01) : 8'h00));

  // ptr_reg update semantics
  assert property (@(posedge clk) disable iff (!reset_n || !past_valid)
                   ptr_we |=> (ptr_reg == $past(ptr_new)));
  assert property (@(posedge clk) disable iff (!reset_n || !past_valid)
                   !ptr_we |=> (ptr_reg == $past(ptr_reg)));

  // Functional effects: increment, reset, wrap
  assert property (@(posedge clk) disable iff (!reset_n || !past_valid)
                   cs |=> (ptr_reg == ($past(ptr_reg) + 8'h01)));
  assert property (@(posedge clk) disable iff (!reset_n || !past_valid)
                   (rst && !cs) |=> (ptr_reg == 8'h00));
  assert property (@(posedge clk) disable iff (!reset_n || !past_valid)
                   (cs && ($past(ptr_reg)==8'hFF)) |=> (ptr_reg == 8'h00));

  // Memory write timing
  assert property (@(posedge clk) disable iff (!past_valid)
                   wr |=> (mem[$past(write_addr)] == $past(write_data)));

  // Read port 0: 1-cycle registered read
  assert property (@(posedge clk) disable iff (!past_valid)
                   tmp_read_data0 == $past(mem[read_addr0]));
  // Output wiring
  assert property (@(posedge clk) read_data0 == tmp_read_data0);

  // Read port 1: combinational read via ptr_reg
  assert property (@(posedge clk) read_data1 == mem[ptr_reg]);

  // Coverage
  cover property (@(posedge clk) rst && !cs);                    // ptr reset path
  cover property (@(posedge clk) cs);                            // increment path
  cover property (@(posedge clk) cs && (ptr_reg==8'hFF));        // wrap opportunity
  cover property (@(posedge clk) rst && cs);                     // simultaneous rst & cs
  cover property (@(posedge clk) wr && (write_addr==read_addr0));// same-cycle RAW hazard

  // Optional: document current RTL behavior when rst & cs both high (cs dominates)
  // cover (rather than assert) to avoid enforcing a potentially unintended spec
  cover property (@(posedge clk) disable iff (!reset_n || !past_valid)
                  rst && cs |=> (ptr_reg == $past(ptr_reg) + 8'h01));

endmodule

bind blockmem2rptr1w blockmem2rptr1w_sva sva_i(.*);
`endif