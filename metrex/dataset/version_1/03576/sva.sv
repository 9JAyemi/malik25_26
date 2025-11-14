// SVA for scrambler
// Bind this module to the DUT for checks and coverage.

module scrambler_sva #(parameter int DATA_BYTE_WIDTH = 4);
  localparam int W = DATA_BYTE_WIDTH*8;

  // Bind ports to DUT internals (including internal regs/wires)
  // Usage: bind scrambler scrambler_sva #(.DATA_BYTE_WIDTH(DATA_BYTE_WIDTH)) u_sva (.*);
  // Assumes names match DUT signals: clk,rst,val_in,data_in,data_out,now,next
  wire                  clk;
  wire                  rst;
  wire                  val_in;
  wire [W-1:0]          data_in;
  wire [W-1:0]          data_out;
  wire [15:0]           now;
  wire [31:0]           next;

  // Elaboration-time sanity
  initial begin
    assert (W >= 1 && W <= 32)
      else $error("scrambler: DATA_BYTE_WIDTH*8 (%0d) must be in 1..32", W);
  end

  // Golden "next" function derived from spec equations
  function automatic logic [31:0] nxt(input logic [15:0] n);
    logic [31:0] t;
    t[31] = n[12]^n[10]^n[7]^n[3]^n[1]^n[0];
    t[30] = n[15]^n[14]^n[12]^n[11]^n[9]^n[6]^n[3]^n[2]^n[0];
    t[29] = n[15]^n[13]^n[12]^n[11]^n[10]^n[8]^n[5]^n[3]^n[2]^n[1];
    t[28] = n[14]^n[12]^n[11]^n[10]^n[9]^n[7]^n[4]^n[2]^n[1]^n[0];
    t[27] = n[15]^n[14]^n[13]^n[12]^n[11]^n[10]^n[9]^n[8]^n[6]^n[1]^n[0];
    t[26] = n[15]^n[13]^n[11]^n[10]^n[9]^n[8]^n[7]^n[5]^n[3]^n[0];
    t[25] = n[15]^n[10]^n[9]^n[8]^n[7]^n[6]^n[4]^n[3]^n[2];
    t[24] = n[14]^n[9]^n[8]^n[7]^n[6]^n[5]^n[3]^n[2]^n[1];
    t[23] = n[13]^n[8]^n[7]^n[6]^n[5]^n[4]^n[2]^n[1]^n[0];
    t[22] = n[15]^n[14]^n[7]^n[6]^n[5]^n[4]^n[1]^n[0];
    t[21] = n[15]^n[13]^n[12]^n[6]^n[5]^n[4]^n[0];
    t[20] = n[15]^n[11]^n[5]^n[4];
    t[19] = n[14]^n[10]^n[4]^n[3];
    t[18] = n[13]^n[9]^n[3]^n[2];
    t[17] = n[12]^n[8]^n[2]^n[1];
    t[16] = n[11]^n[7]^n[1]^n[0];

    t[15] = n[15]^n[14]^n[12]^n[10]^n[6]^n[3]^n[0];
    t[14] = n[15]^n[13]^n[12]^n[11]^n[9]^n[5]^n[3]^n[2];
    t[13] = n[14]^n[12]^n[11]^n[10]^n[8]^n[4]^n[2]^n[1];
    t[12] = n[13]^n[11]^n[10]^n[9]^n[7]^n[3]^n[1]^n[0];
    t[11] = n[15]^n[14]^n[10]^n[9]^n[8]^n[6]^n[3]^n[2]^n[0];
    t[10] = n[15]^n[13]^n[12]^n[9]^n[8]^n[7]^n[5]^n[3]^n[2]^n[1];
    t[9]  = n[14]^n[12]^n[11]^n[8]^n[7]^n[6]^n[4]^n[2]^n[1]^n[0];
    t[8]  = n[15]^n[14]^n[13]^n[12]^n[11]^n[10]^n[7]^n[6]^n[5]^n[1]^n[0];
    t[7]  = n[15]^n[13]^n[11]^n[10]^n[9]^n[6]^n[5]^n[4]^n[3]^n[0];
    t[6]  = n[15]^n[10]^n[9]^n[8]^n[5]^n[4]^n[2];
    t[5]  = n[14]^n[9]^n[8]^n[7]^n[4]^n[3]^n[1];
    t[4]  = n[13]^n[8]^n[7]^n[6]^n[3]^n[2]^n[0];
    t[3]  = n[15]^n[14]^n[7]^n[6]^n[5]^n[3]^n[2]^n[1];
    t[2]  = n[14]^n[13]^n[6]^n[5]^n[4]^n[2]^n[1]^n[0];
    t[1]  = n[15]^n[14]^n[13]^n[5]^n[4]^n[1]^n[0];
    t[0]  = n[15]^n[13]^n[4]^n[0];
    return t;
  endfunction

  // Convenience lets
  let exp_next  = nxt(now);
  let exp_mask  = exp_next[W-1:0];
  let exp_state = nxt($past(now))[31:16];

  // Clocking: sample on posedge
  // Reset is synchronous; use overlapped implications

  // Reset behavior: when rst=1 at clock edge, now must be reset value
  assert property (@(posedge clk) rst |-> now == 16'hf0f6);

  // Hold when !val_in
  assert property (@(posedge clk) !rst && !val_in |-> now == $past(now));

  // Advance when val_in
  assert property (@(posedge clk) !rst && val_in |-> now == exp_state);

  // Combinational next correctness vs spec
  assert property (@(posedge clk) next == exp_next);

  // Output function
  assert property (@(posedge clk) data_out == (val_in ? (data_in ^ exp_mask) : data_in));

  // No X after reset deasserted
  assert property (@(posedge clk) !rst |-> !$isunknown(now));
  assert property (@(posedge clk) !rst |-> !$isunknown(data_out));

  // Coverage
  cover property (@(posedge clk) rst ##1 !rst ##1 val_in);                  // reset then advance
  cover property (@(posedge clk) !rst && !val_in ##1 val_in);               // hold then advance
  cover property (@(posedge clk) !rst && val_in ##1 val_in);                // back-to-back advances
  cover property (@(posedge clk) !rst && val_in && (exp_mask != '0) &&
                               (data_out != data_in));                      // actual scrambling occurs
endmodule

// Example bind (place in a bind file or testbench):
// bind scrambler scrambler_sva #(.DATA_BYTE_WIDTH(DATA_BYTE_WIDTH)) u_scrambler_sva (.*);