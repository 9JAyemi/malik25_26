// SVA for bit_reversal. Concise, parametric, and bindable.
// Drop into a separate file and compile with the DUT.

module bit_reversal_sva
  #(parameter int DATA_SIZE = 32)
(
  input  logic [DATA_SIZE-1:0] data_in,
  input  logic [DATA_SIZE-1:0] data_out,
  input  logic [1:0]           rev_type
);

  // Encoding (match DUT)
  localparam logic [1:0] NO_REVERSE = 2'b00;
  localparam logic [1:0] BYTE       = 2'b01;
  localparam logic [1:0] HALF_WORD  = 2'b10;
  localparam logic [1:0] WORD       = 2'b11;

  // Sanity/shape checks (immediate)
  initial begin
    assert (DATA_SIZE % 4 == 0 && DATA_SIZE >= 4)
      else $fatal(1, "bit_reversal: DATA_SIZE must be >=4 and divisible by 4 (got %0d)", DATA_SIZE);
  end

  // Helper functions to compute expected output
  function automatic int group_size(input int t);
    if (t == 0) group_size = 1;
    else        group_size = (DATA_SIZE/4) << (t-1); // 1: N/4, 2: N/2, 3: N
  endfunction

  function automatic logic [DATA_SIZE-1:0] reverse_by_type
    (input logic [DATA_SIZE-1:0] din, input int t);
    logic [DATA_SIZE-1:0] dout;
    int S, i, idx;
    S = group_size(t);
    if (t == 0) begin
      dout = din;
    end else begin
      for (i = 0; i < DATA_SIZE; i++) begin
        idx   = S*((i/S)+1) - 1 - (i%S);
        dout[i] = din[idx];
      end
    end
    reverse_by_type = dout;
  endfunction

  // Control must be known
  assert property ( !$isunknown(rev_type) )
    else $error("bit_reversal: rev_type contains X/Z");

  // Core functional checks (clockless, combinational consistency)
  assert property ( (rev_type == NO_REVERSE) |-> (data_out == data_in) )
    else $error("bit_reversal: NO_REVERSE mismatch");

  assert property ( (rev_type == BYTE) |-> (data_out == reverse_by_type(data_in, 1)) )
    else $error("bit_reversal: BYTE reverse mismatch");

  assert property ( (rev_type == HALF_WORD) |-> (data_out == reverse_by_type(data_in, 2)) )
    else $error("bit_reversal: HALF_WORD reverse mismatch");

  assert property ( (rev_type == WORD) |-> (data_out == reverse_by_type(data_in, 3)) )
    else $error("bit_reversal: WORD reverse mismatch");

  // Optional: ensure grouping sizes divide width (robustness for non-default DATA_SIZE)
  generate
    genvar t;
    for (t = 1; t <= 3; t++) begin : g_div
      initial assert (DATA_SIZE % group_size(t) == 0)
        else $fatal(1, "bit_reversal: group_size(%0d)=%0d does not divide DATA_SIZE=%0d", t, group_size(t), DATA_SIZE);
    end
  endgenerate

  // Coverage (ensure each mode exercised with correct result)
  cover property (rev_type == NO_REVERSE && data_out == data_in);
  cover property (rev_type == BYTE       && data_out == reverse_by_type(data_in, 1));
  cover property (rev_type == HALF_WORD  && data_out == reverse_by_type(data_in, 2));
  cover property (rev_type == WORD       && data_out == reverse_by_type(data_in, 3));

endmodule

// Bind into DUT
bind bit_reversal bit_reversal_sva #(.DATA_SIZE(DATA_SIZE))
  bit_reversal_sva_i(.data_in(data_in), .data_out(data_out), .rev_type(rev_type));