// SVA checker for arithshiftbidir
`ifndef ARITHSHIFTBIDIR_SVA_SV
`define ARITHSHIFTBIDIR_SVA_SV

module arithshiftbidir_sva #(
  parameter int lpm_width     = 32,
  parameter int lpm_widthdist = 5
)(
  input  logic [lpm_widthdist-1:0] distance,
  input  logic signed [lpm_width-1:0] data,
  input  logic                      direction,
  input  logic [lpm_width-1:0]      result
);
  localparam int W = lpm_width;

  logic [W-1:0] ref_lsh;
  logic [W-1:0] ref_arsh;

  assign ref_lsh  = data << distance;
  assign ref_arsh = $unsigned($signed(data) >>> distance);

  // Combinational immediate assertions (no clock required)
  always_comb begin
    // Main functional equivalence
    assert (result == (direction ? ref_arsh : ref_lsh))
      else $error("arithshiftbidir: result mismatch dir=%0b dist=%0d data=%0h exp=%0h got=%0h",
                  direction, distance, data, (direction ? ref_arsh : ref_lsh), result);

    // Direction-specific checks
    if (!direction) begin
      assert (result == (data << distance))
        else $error("arithshiftbidir: left shift mismatch");
      // Zero-fill on right for left shift with nonzero distance
      if ($unsigned(distance) > 0)
        assert (result[$unsigned(distance)-1:0] == '0)
          else $error("arithshiftbidir: LSL zero-fill violated");
    end
    else begin
      assert (result == $unsigned($signed(data) >>> distance))
        else $error("arithshiftbidir: arithmetic right shift mismatch");
      // Check both rsh and rshN behaviors match
      if (data[W-1] == 1'b0)
        assert (result == (data >> distance))
          else $error("arithshiftbidir: logical RSH (non-neg) mismatch");
      else
        assert (result == ~(~data >> distance))
          else $error("arithshiftbidir: RSH via invert trick (neg) mismatch");
      // Sign-bit preserved on arithmetic right shift when dist>0
      if ($unsigned(distance) > 0)
        assert (result[W-1] == data[W-1])
          else $error("arithshiftbidir: ARSH sign-bit not preserved");
    end

    // Distance==0 -> pass-through
    if (distance == '0)
      assert (result == data)
        else $error("arithshiftbidir: dist==0 must pass-through");

    // Large distances (>= width)
    if ($unsigned(distance) >= W) begin
      if (!direction)
        assert (result == '0)
          else $error("arithshiftbidir: LSL with dist>=W must be 0");
      else
        assert (result == {W{data[W-1]}})
          else $error("arithshiftbidir: ARSH with dist>=W must be all sign");
    end
  end

  // Lightweight functional coverage (immediate cover statements)
  cover (direction == 0);
  cover (direction == 1);
  cover (distance == '0);
  cover (distance == W-1);
  cover (!direction && (distance == 1));
  cover (direction && data[W-1] == 1'b0 && (distance == 1));
  cover (direction && data[W-1] == 1'b1 && (distance == 1));

endmodule

// Bind checker into DUT; parameters propagate from instance
bind arithshiftbidir arithshiftbidir_sva #(
  .lpm_width(lpm_width),
  .lpm_widthdist(lpm_widthdist)
) (
  .distance(distance),
  .data(data),
  .direction(direction),
  .result(result)
);

`endif