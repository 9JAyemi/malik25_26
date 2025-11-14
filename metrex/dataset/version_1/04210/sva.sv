// SVA for constmuldivmod
// Bind this module to the DUT instance
module constmuldivmod_sva(input logic [7:0] A, input logic [5:0] mode, input logic [7:0] Y);

  event ev = $global_clock;

  // Helper: signed div by 2^k with truncation toward zero (no "/" used)
  function automatic signed [8:0] qdiv_p2(input signed [7:0] a, input int k);
    automatic signed [8:0] q;
    automatic logic [7:0] mask;
    q    = a >>> k;                      // arithmetic shift (toward -inf)
    mask = (k == 0) ? 8'h00 : ((8'h1 << k) - 1);
    if ((k > 0) && a[7] && ((a & mask) != 0)) q = q + 1;  // bias toward zero
    return q;                             // 9-bit to avoid intermediate overflow
  endfunction

  // Helper: signed mod by 2^k consistent with SystemVerilog remainder semantics
  function automatic signed [8:0] rmod_p2(input signed [7:0] a, input int k);
    automatic signed [8:0] q;
    q = qdiv_p2(a, k);
    return a - (q <<< k);                 // r has same sign as a, |r|<2^k
  endfunction

  // No X on Y unless dividing/modding by zero
  assert property (@(ev)
    (!$isunknown({A,mode})) && !(mode inside {6'd0,6'd1,6'd15,6'd16,6'd30,6'd31})
    |-> !$isunknown(Y)
  );

  // Default clause
  assert property (@(ev) disable iff ($isunknown({A,mode}))
    !(mode inside {[6'd0:6'd44]}) |-> (Y == (A << 4))
  );

  // Unsigned ops (modes 0..14)
  assert property (@(ev) mode == 6'd0  |-> $isunknown(Y));                     // A/0
  assert property (@(ev) mode == 6'd1  |-> $isunknown(Y));                     // A%0
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd2  |-> (Y == 8'h00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd3  |-> (Y == A));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd4  |-> (Y == 8'h00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd5  |-> (Y == A));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd6  |-> (Y == (A >> 1)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd7  |-> (Y == {7'h00, A[0]}));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd8  |-> (Y == (A << 1)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd9  |-> (Y == (A >> 2)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd10 |-> (Y == {6'h00, A[1:0]}));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd11 |-> (Y == (A << 2)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd12 |-> (Y == (A >> 3)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd13 |-> (Y == {5'h00, A[2:0]}));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd14 |-> (Y == (A << 3)));

  // Signed ops, +0/+1/+2/+4/+8 (modes 15..29)
  assert property (@(ev) mode == 6'd15 |-> $isunknown(Y));                     // / +0
  assert property (@(ev) mode == 6'd16 |-> $isunknown(Y));                     // % +0
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd17 |-> (Y == 8'h00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd18 |-> ($signed(Y) == $signed(A)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd19 |-> ($signed(Y) == 8'sh00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd20 |-> ($signed(Y) == $signed(A)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd21 |-> ($signed(Y) == $signed(qdiv_p2($signed(A),1)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd22 |-> ($signed(Y) == $signed(rmod_p2($signed(A),1)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd23 |-> (Y == (A << 1)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd24 |-> ($signed(Y) == $signed(qdiv_p2($signed(A),2)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd25 |-> ($signed(Y) == $signed(rmod_p2($signed(A),2)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd26 |-> (Y == (A << 2)));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd27 |-> ($signed(Y) == $signed(qdiv_p2($signed(A),3)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd28 |-> ($signed(Y) == $signed(rmod_p2($signed(A),3)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd29 |-> (Y == (A << 3)));

  // Signed ops, -0/-1/-2/-4/-8 (modes 30..44)
  assert property (@(ev) mode == 6'd30 |-> $isunknown(Y));                     // / -0 (==0)
  assert property (@(ev) mode == 6'd31 |-> $isunknown(Y));                     // % -0 (==0)
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd32 |-> (Y == 8'h00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd33 |-> ($signed(Y) == $signed(8'(-$signed(A))))); // divide by -1
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd34 |-> ($signed(Y) == 8'sh00));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd35 |-> ($signed(Y) == $signed(8'(-$signed(A)))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd36 |-> ($signed(Y) == $signed(8'(-$signed(qdiv_p2($signed(A),1)[7:0])))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd37 |-> ($signed(Y) == $signed(rmod_p2($signed(A),1)[7:0]))); // remainder same as +2
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd38 |-> ($signed(Y) == $signed(8'(-($signed(A) <<< 1)))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd39 |-> ($signed(Y) == $signed(8'(-$signed(qdiv_p2($signed(A),2)[7:0])))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd40 |-> ($signed(Y) == $signed(rmod_p2($signed(A),2)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd41 |-> ($signed(Y) == $signed(8'(-($signed(A) <<< 2)))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd42 |-> ($signed(Y) == $signed(8'(-$signed(qdiv_p2($signed(A),3)[7:0])))));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd43 |-> ($signed(Y) == $signed(rmod_p2($signed(A),3)[7:0])));
  assert property (@(ev) disable iff ($isunknown({A,mode})) mode == 6'd44 |-> ($signed(Y) == $signed(8'(-($signed(A) <<< 3)))));

  // Coverage: hit every mode and key corner A values
  genvar i;
  generate
    for (i = 0; i <= 44; i++) begin : cov_modes
      cover property (@(ev) mode == 6'(i));
    end
  endgenerate
  cover property (@(ev) (A == 8'h00));
  cover property (@(ev) (A == 8'h01));
  cover property (@(ev) (A == 8'hFF)); // -1
  cover property (@(ev) (A == 8'h80)); // -128
  cover property (@(ev) (A == 8'h7F));
  // Bias cases for signed div by powers of two (odd negatives)
  cover property (@(ev) (mode inside {6'd21,6'd24,6'd27}) && $signed(A) < 0 && ((A & 8'h01) != 0));
  cover property (@(ev) (mode inside {6'd36,6'd39,6'd42}) && $signed(A) < 0 && ((A & 8'h01) != 0));

endmodule

bind constmuldivmod constmuldivmod_sva (.A(A), .mode(mode), .Y(Y));