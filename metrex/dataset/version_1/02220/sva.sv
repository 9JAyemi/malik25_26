// SVA binders for the given design

// Barrel shifter assertions and coverage
module barrel_shifter_sva(input logic [3:0] data,
                          input logic [1:0] shift,
                          input logic [3:0] out);
  // Functional equivalence and X checks
  always_comb begin
    if (!$isunknown({data,shift})) begin
      assert (
          ((shift==2'b00) && (out===data)) ||
          ((shift==2'b01) && (out==={data[2:0],data[3]})) ||
          ((shift==2'b10) && (out==={data[1:0],data[3:2]})) ||
          ((shift==2'b11) && (out==={data[0],data[3:1]}))
        ) else $error("barrel_shifter: out mismatch for shift=%b data=%b out=%b", shift, data, out);
      assert (!$isunknown(out)) else $error("barrel_shifter: X/Z on out");
    end
  end

  // Cover all shift selections (functional reachability)
  cover property (@(*) shift==2'b00);
  cover property (@(*) shift==2'b01);
  cover property (@(*) shift==2'b10);
  cover property (@(*) shift==2'b11);

  // Example wrap-around cover
  cover property (@(*) (data==4'b1000 && shift==2'b01 && out==4'b0001));
endmodule

// Two's complement assertions and coverage
module twos_complement_sva(input logic [3:0] in,
                           input logic [3:0] out);
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out === ((~in) + 4'd1))
        else $error("twos_complement: mismatch in=%b out=%b", in, out);
      assert (!$isunknown(out))
        else $error("twos_complement: X/Z on out");
      // in + out should equal 16 (carry-out 1, sum 0) in 4-bit arithmetic
      assert ({1'b0,in} + {1'b0,out} == 5'b10000)
        else $error("twos_complement: in+out != 16 (mod-16) in=%b out=%b", in, out);
    end
  end

  // Corner covers
  cover property (@(*) in==4'h0 && out==4'h0);
  cover property (@(*) in==4'h8 && out==4'h8);
  cover property (@(*) in==4'hF && out==4'h1);
endmodule

// Top-level composition assertions and coverage
module top_module_sva(input  logic [3:0] in,
                      input  logic [3:0] out,
                      input  logic [3:0] wire_bs_out,
                      input  logic [1:0] bs_shift);
  logic [3:0] rot1;
  assign rot1 = {in[2:0], in[3]};

  // Shift constant tie-off check (should be 1)
  always_comb begin
    assert (bs_shift===2'b01)
      else $error("top_module: barrel_shifter shift not tied to 2'b01 (got %b)", bs_shift);
  end

  // End-to-end functional checks and X-propagation discipline
  always_comb begin
    if (!$isunknown(in)) begin
      assert (wire_bs_out === rot1)
        else $error("top_module: bs_out mismatch. in=%b bs_out=%b", in, wire_bs_out);
      assert (out === ((~rot1) + 4'd1))
        else $error("top_module: out mismatch vs two's complement of rot1. in=%b rot1=%b out=%b",
                    in, rot1, out);
      assert (!$isunknown(wire_bs_out) && !$isunknown(out))
        else $error("top_module: X/Z detected on bs_out/out");
    end
  end

  // Representative end-to-end covers
  cover property (@(*) in==4'b0001 && wire_bs_out==4'b0010 && out==((~4'b0010)+4'd1));
  cover property (@(*) in==4'b1000 && wire_bs_out==4'b0001 && out==((~4'b0001)+4'd1));
endmodule

// Bind the SVA to the DUTs
bind barrel_shifter   barrel_shifter_sva bs_sva_i(.data(data), .shift(shift), .out(out));
bind twos_complement  twos_complement_sva tc_sva_i(.in(in), .out(out));
// Pass internal bs.shift up to the top-level SVA to ensure the constant tie-off is checked
bind top_module       top_module_sva top_sva_i(.in(in), .out(out), .wire_bs_out(wire_bs_out), .bs_shift(bs.shift));