// SVA checker for priority_encoder
module priority_encoder_sva (
  input logic [15:0] I,
  input logic        EN,
  input logic [3:0]  O,
  input logic [3:0]  temp
);

  default clocking cb @(posedge EN); endclocking

  // Helper decode to mirror DUT case statement
  function automatic logic [3:0] decode(input logic [3:0] t);
    case (t)
      4'b0001: decode = 4'b0001;
      4'b0010: decode = 4'b0010;
      4'b0100: decode = 4'b0100;
      4'b1000: decode = 4'b1000;
      default: decode = 4'b0000;
    endcase
  endfunction

  // Nibble comparisons as in DUT arithmetic
  logic a1, a2;
  assign a1 = (I[15:12] > I[11:8]);
  assign a2 = (I[7:4]   > I[3:0]);

  // On posedge EN, temp must update (via NBA) to {000, a1 & ~a2}
  property p_temp_update;
    disable iff ($isunknown({EN,I}))
    1 |-> ##0 (temp == {3'b000, (a1 & ~a2)});
  endproperty
  assert property (p_temp_update);

  // Upper bits of temp must be zero after update
  property p_temp_upper_zero;
    disable iff ($isunknown(temp))
    1 |-> ##0 (temp[3:1] == 3'b000);
  endproperty
  assert property (p_temp_upper_zero);

  // Decode correctness: O must be the case-decode of temp
  always_comb begin
    if (!$isunknown(temp)) assert (O == decode(temp))
      else $error("O != decode(temp)");
  end

  // O must be onehot or zero
  always_comb begin
    if (!$isunknown(O)) assert ($onehot0(O))
      else $error("O is not onehot0");
  end

  // No X-propagation when inputs are known at update
  property p_no_x_after_update;
    disable iff ($isunknown({EN,I}))
    1 |-> ##0 (!$isunknown(temp) && !$isunknown(O));
  endproperty
  assert property (p_no_x_after_update);

  // Functional coverage
  // Exercise all comparator outcome combinations
  cover property (cb) (a1==0 && a2==0);
  cover property (cb) (a1==0 && a2==1);
  cover property (cb) (a1==1 && a2==0); // only case that makes temp==0001
  cover property (cb) (a1==1 && a2==1);

  // Observe produced O values
  cover property (cb) (O == 4'b0000);
  cover property (cb) (O == 4'b0001);
  cover property (cb) (O == 4'b0010); // should remain unreachable with given RTL
  cover property (cb) (O == 4'b0100); // should remain unreachable with given RTL
  cover property (cb) (O == 4'b1000); // should remain unreachable with given RTL

endmodule

// Bind into DUT
bind priority_encoder priority_encoder_sva sva_i(.I(I), .EN(EN), .O(O), .temp(temp));