// SVA for wb_ram_block. Bind this to the DUT.
// Focus: protocol, timing, data correctness, and essential coverage.

module wb_ram_block_sva #(parameter AWIDTH=9)
(
  input  logic              clk_i,
  input  logic              stb_i,
  input  logic              we_i,
  input  logic [AWIDTH-1:0] adr_i,
  input  logic [31:0]       dat_i,
  input  logic [31:0]       dat_o,
  input  logic              ack_o
);

  default clocking cb @(posedge clk_i); endclocking

  // Lightweight scoreboard mirroring DUT write behavior (no reset in DUT)
  logic [31:0] model_mem [0:(1<<AWIDTH)-1];
  bit          model_val [0:(1<<AWIDTH)-1];

  always_ff @(posedge clk_i) begin
    if (stb_i && we_i) begin
      model_mem[adr_i] <= dat_i;
      model_val[adr_i] <= 1'b1;
    end
  end

  // Basic handshake sanity
  assert property (ack_o |-> stb_i);                 // no ack without strobe
  assert property (!stb_i |-> !ack_o);               // ack must be 0 when strobe is 0

  // Write behavior
  assert property (stb_i && we_i |-> ack_o);         // write is immediately acked (combinational)

  // Read behavior: 1-cycle latency, single-cycle pulse when stb held
  assert property ($rose(stb_i) && !we_i |-> !ack_o);                                        // no read ack on first cycle
  assert property ($past(stb_i && !we_i && !ack_o) && stb_i && !we_i |-> ack_o);             // read ack on second cycle if stb held
  assert property (ack_o && !we_i |-> !$past(ack_o));                                        // read ack is not asserted back-to-back
  assert property ((stb_i && !we_i && !ack_o) |-> $stable(adr_i) until_with (ack_o || !stb_i)); // address stable while read pending
  assert property ((stb_i && !ack_o) |-> $stable(we_i));                                     // WE stable while waiting for ack

  // Data timing/correctness (dat_o shows memory[adr_i] from previous cycle)
  assert property ($past(model_val[adr_i]) |-> (dat_o == $past(model_mem[adr_i])));

  // Knownness on critical events
  assert property (stb_i && we_i |-> !$isunknown(ack_o));                                    // write ack is determinate
  assert property (ack_o && !we_i && $past(model_val[adr_i]) |-> !$isunknown(dat_o));        // read data known if previously written

  // Coverage: write, read, pipeline behavior, and data return
  cover property (stb_i && we_i && ack_o);                                                   // a write transaction
  cover property ($rose(stb_i) && !we_i ##1 (stb_i && !we_i && ack_o));                      // a read transaction (two-cycle)
  cover property ($rose(stb_i) && !we_i ##1 (stb_i && !we_i && ack_o) ##1
                  (stb_i && !we_i && !ack_o) ##1 (stb_i && !we_i && ack_o));                // pipelined back-to-back reads (ack every other cycle)
  cover property ( (stb_i && we_i) ##1 (stb_i && !we_i) ##1 (ack_o && (dat_o == $past(model_mem[adr_i]))) ); // write then read returns data

endmodule

// Bind into DUT (tool-dependent instance naming may vary)
bind wb_ram_block wb_ram_block_sva #(.AWIDTH(AWIDTH)) i_wb_ram_block_sva
(
  .clk_i(clk_i),
  .stb_i(stb_i),
  .we_i(we_i),
  .adr_i(adr_i),
  .dat_i(dat_i),
  .dat_o(dat_o),
  .ack_o(ack_o)
);