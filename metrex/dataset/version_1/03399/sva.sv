// SVA for arbiter. Bind into DUT.
// Focus: reset behavior, one-hot/valid consistency, priority/eligibility,
// encoded mapping, and key functional coverage.

module arbiter_sva (
  input clk, rst,
  input [3:0] request, acknowledge,
  input [3:0] grant,
  input       grant_valid,
  input [1:0] grant_encoded
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  wire [3:0] elig = request & ~acknowledge;

  // Reset behavior (checked during reset)
  assert property (@cb rst |-> (grant==4'b0000 && !grant_valid && grant_encoded==2'b00) throughout rst);

  // Structural sanity
  assert property (@cb $onehot0(grant));
  assert property (@cb grant_valid == (grant != 4'b0000));

  // Grant implies request active and not acknowledged
  genvar i;
  generate
    for (i=0;i<4;i++) begin : G_IMP
      assert property (@cb grant[i] |-> (request[i] && !acknowledge[i]));
    end
  endgenerate

  // Priority/select behavior (next-cycle result from current elig)
  assert property (@cb  elig[0]                         |-> (grant==4'b0001 && grant_valid && grant_encoded==2'b01));
  assert property (@cb !elig[0] &&  elig[1]             |-> (grant==4'b0010 && grant_valid && grant_encoded==2'b10));
  assert property (@cb !elig[0] && !elig[1] &&  elig[2] |-> (grant==4'b0100 && grant_valid && grant_encoded==2'b11));
  assert property (@cb !elig[0] && !elig[1] && !elig[2] && elig[3]
                                                      |-> (grant==4'b1000 && grant_valid && grant_encoded==2'b11));
  assert property (@cb (elig==4'b0000)                 |-> (grant==4'b0000 && !grant_valid && grant_encoded==2'b00));

  // Encoded mapping must match granted bit (as implemented)
  assert property (@cb (grant==4'b0001) |-> (grant_encoded==2'b01 && grant_valid));
  assert property (@cb (grant==4'b0010) |-> (grant_encoded==2'b10 && grant_valid));
  assert property (@cb (grant==4'b0100) |-> (grant_encoded==2'b11 && grant_valid));
  assert property (@cb (grant==4'b1000) |-> (grant_encoded==2'b11 && grant_valid));
  assert property (@cb (grant==4'b0000) |-> (grant_encoded==2'b00 && !grant_valid));

  // Key functional coverage
  cover property (@cb elig[0]                         |-> grant==4'b0001); // grant ch0
  cover property (@cb !elig[0] &&  elig[1]            |-> grant==4'b0010); // grant ch1
  cover property (@cb !elig[0] && !elig[1] &&  elig[2]|-> grant==4'b0100); // grant ch2
  cover property (@cb !elig[0] && !elig[1] && !elig[2]&&  elig[3]|-> grant==4'b1000); // grant ch3
  cover property (@cb elig==4'b0000                   |-> grant==4'b0000); // no grant

  // Priority override when multiple eligibles
  cover property (@cb (elig[0] && elig[1]) |-> grant==4'b0001);
  cover property (@cb (!elig[0] && elig[1] && elig[2]) |-> grant==4'b0010);
  cover property (@cb (!elig[0] && !elig[1] && elig[2] && elig[3]) |-> grant==4'b0100);

  // Acknowledge masks a request
  cover property (@cb (!elig[0] && request[1] && acknowledge[1]) ##1 (grant!=4'b0010));
endmodule

bind arbiter arbiter_sva u_arbiter_sva (.*);