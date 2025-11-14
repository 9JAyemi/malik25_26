// SVA for lsu_dc_parity_gen
// Checks per-chunk XOR parity correctness, locality, knownness, and basic coverage.
// Bind this file to the DUT.

module lsu_dc_parity_gen_sva #(
  parameter int WIDTH = 8,
  parameter int NUM   = 16
) (
  input  logic [WIDTH*NUM-1:0] data_in,
  input  logic [NUM-1:0]       parity_out
);

  // Compile-time sanity
  initial begin
    assert (WIDTH > 0 && NUM > 0)
      else $error("lsu_dc_parity_gen: WIDTH and NUM must be > 0");
  end

  localparam int TOT = WIDTH*NUM;
  localparam logic ALL1_PAR = (WIDTH & 1) ? 1'b1 : 1'b0;

  genvar gi;
  generate
    for (gi = 0; gi < NUM; gi++) begin : G
      wire [WIDTH-1:0] s = data_in[WIDTH*gi +: WIDTH];

      // Functional correctness when inputs are known
      // Use ##0 to avoid race with combinational update
      assert property (@(data_in) (!$isunknown(s)) |-> ##0 (parity_out[gi] == ^s))
        else $error("Parity mismatch on group %0d", gi);

      // Output knownness when inputs are known
      assert property (@(data_in) (!$isunknown(s)) |-> ##0 (!$isunknown(parity_out[gi])))
        else $error("Parity_out[%0d] X/Z with known inputs", gi);

      // Locality: parity_out[gi] only changes if its own slice changes
      assert property (@(data_in) $changed(parity_out[gi]) |-> !$stable(s))
        else $error("Parity_out[%0d] changed without its slice changing", gi);

      // No spurious change: if slice is stable this event, parity bit is stable
      assert property (@(data_in) $stable(s) |-> ##0 $stable(parity_out[gi]))
        else $error("Parity_out[%0d] changed while its slice was stable", gi);

      // Coverage: hit both parity values
      cover property (@(data_in) ##0 (parity_out[gi] == 1'b0));
      cover property (@(data_in) ##0 (parity_out[gi] == 1'b1));

      // Coverage: corner patterns (all 0s, one-hot, all 1s)
      cover property (@(data_in) (! $isunknown(s) && (s == '0)) ##0 (parity_out[gi] == 1'b0));
      cover property (@(data_in) (! $isunknown(s) && $onehot(s)) ##0 (parity_out[gi] == 1'b1));
      cover property (@(data_in) (! $isunknown(s) && (s == {WIDTH{1'b1}})) ##0 (parity_out[gi] == ALL1_PAR));
    end
  endgenerate

endmodule

// Bind into the DUT
bind lsu_dc_parity_gen lsu_dc_parity_gen_sva #(.WIDTH(WIDTH), .NUM(NUM)) u_lsu_dc_parity_gen_sva (.data_in(data_in), .parity_out(parity_out));