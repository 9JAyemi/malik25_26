// SVA checker for RF. Bind this into the RF module.
// Concise, functionally complete equivalence + key X-prop and coverage.

`ifndef RF_SVA
`define RF_SVA

bind RF RF_sva rf_sva();

module RF_sva;

  // Golden recompute from only DUT IOs
  logic [7:0] f0_6, f1_4, f0_2, f1_0;
  logic [7:0] mv3, mv2, mv1, mv0;
  logic [7:0] e7, e6, e5, e4, e3, e2, e1, e0;
  logic [63:0] exp_o;

  always_comb begin
    // Fold functions
    f0_6 = {i_rf_in[54:48],i_rf_in[55]} ^
           {i_rf_in[53:48],i_rf_in[55:54]} ^
           {i_rf_in[48],i_rf_in[55:49]};
    f1_4 = {i_rf_in[36:32],i_rf_in[39:37]} ^
           {i_rf_in[35:32],i_rf_in[39:36]} ^
           {i_rf_in[33:32],i_rf_in[39:34]};
    f0_2 = {i_rf_in[22:16],i_rf_in[23]} ^
           {i_rf_in[21:16],i_rf_in[23:22]} ^
           {i_rf_in[16],i_rf_in[23:17]};
    f1_0 = {i_rf_in[4:0],i_rf_in[7:5]} ^
           {i_rf_in[3:0],i_rf_in[7:4]} ^
           {i_rf_in[1:0],i_rf_in[7:2]};

    // Byte moves
    mv3 = (i_op==1'b0) ? (i_rf_in[63:56] ^ (f0_6 + i_rsk[31:24]))
                       : (i_rf_in[63:56] ^ (f0_6 + i_rsk[7:0]));
    mv2 = (i_op==1'b0) ? (i_rf_in[47:40] + (f1_4 ^ i_rsk[23:16]))
                       : (i_rf_in[47:40] - (f1_4 ^ i_rsk[15:8]));
    mv1 = (i_op==1'b0) ? (i_rf_in[31:24] ^ (f0_2 + i_rsk[15:8]))
                       : (i_rf_in[31:24] ^ (f0_2 + i_rsk[23:16]));
    mv0 = (i_op==1'b0) ? (i_rf_in[15:8]  + (f1_0 ^ i_rsk[7:0]))
                       : (i_rf_in[15:8]  - (f1_0 ^ i_rsk[31:24]));

    // Output byte muxing
    e7 = (i_rf_final) ? mv3
                      : ((i_op==1'b0) ? i_rf_in[55:48] : i_rf_in[7:0]);
    e6 = (i_rf_final) ? i_rf_in[55:48]
                      : ((i_op==1'b0) ? mv2 : mv3);
    e5 = (i_rf_final) ? mv2
                      : ((i_op==1'b0) ? i_rf_in[39:32] : i_rf_in[55:48]);
    e4 = (i_rf_final) ? i_rf_in[39:32]
                      : ((i_op==1'b0) ? mv1 : mv2);
    e3 = (i_rf_final) ? mv1
                      : ((i_op==1'b0) ? i_rf_in[23:16] : i_rf_in[39:32]);
    e2 = (i_rf_final) ? i_rf_in[23:16]
                      : ((i_op==1'b0) ? mv0 : mv1);
    e1 = (i_rf_final) ? mv0
                      : ((i_op==1'b0) ? i_rf_in[7:0] : i_rf_in[23:16]);
    e0 = (i_rf_final) ? i_rf_in[7:0]
                      : ((i_op==1'b0) ? mv3 : mv0);

    exp_o = {e7,e6,e5,e4,e3,e2,e1,e0};

    // Functional equivalence
    assert (o_rf_out === exp_o)
      else $error("RF: o_rf_out mismatch. i_op=%0b i_rf_final=%0b exp=%h got=%h",
                  i_op, i_rf_final, exp_o, o_rf_out);

    // Known-inputs imply known-output (X/Z guard)
    if (!$isunknown({i_op,i_rf_final,i_rsk,i_rf_in})) begin
      assert (!$isunknown(o_rf_out))
        else $error("RF: X/Z on o_rf_out with known inputs");
    end

    // Optional internal wiring consistency (uncomment if desired)
    // assert ({w_rf_out7,w_rf_out6,w_rf_out5,w_rf_out4,w_rf_out3,w_rf_out2,w_rf_out1,w_rf_out0} === w_rf_out);

    // Coverage: control combinations
    cover (i_op==0 && i_rf_final==0);
    cover (i_op==0 && i_rf_final==1);
    cover (i_op==1 && i_rf_final==0);
    cover (i_op==1 && i_rf_final==1);

    // Coverage: arithmetic overflow (add) / borrow (sub) on 8-bit ops
    if (i_op==0) begin
      automatic logic [8:0] sum2 = {1'b0,i_rf_in[47:40]} + {1'b0,(f1_4 ^ i_rsk[23:16])};
      automatic logic [8:0] sum0 = {1'b0,i_rf_in[15:8]}  + {1'b0,(f1_0 ^ i_rsk[7:0])};
      cover (sum2[8]);
      cover (sum0[8]);
    end else begin
      automatic logic [8:0] diff2 = {1'b0,i_rf_in[47:40]} - {1'b0,(f1_4 ^ i_rsk[15:8])};
      automatic logic [8:0] diff0 = {1'b0,i_rf_in[15:8]}  - {1'b0,(f1_0 ^ i_rsk[31:24])};
      cover (diff2[8]);
      cover (diff0[8]);
    end
  end

endmodule

`endif