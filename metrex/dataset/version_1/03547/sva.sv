// SVA for decoder_4to16_pipeline
// Bind-in module; no DUT edits required

`ifndef DECODER_4TO16_PIPELINE_SVA
`define DECODER_4TO16_PIPELINE_SVA

module decoder_4to16_pipeline_sva
(
    input  logic        A, B,
    input  logic [15:0] Y,
    input  logic [1:0]  stage1_A, stage1_B,
    input  logic [3:0]  stage2_A, stage2_B,
    input  logic [7:0]  stage3_A, stage3_B
);

    // Structural zero-extend pipeline checks (delta-cycle safe via ##0)
    assert property (@(A or stage1_A) 1 |-> ##0 (stage1_A === {1'b0, A}));
    assert property (@(B or stage1_B) 1 |-> ##0 (stage1_B === {1'b0, B}));

    assert property (@(stage1_A or stage2_A) 1 |-> ##0 (stage2_A === {2'b00, stage1_A}));
    assert property (@(stage1_B or stage2_B) 1 |-> ##0 (stage2_B === {2'b00, stage1_B}));

    assert property (@(stage2_A or stage3_A) 1 |-> ##0 (stage3_A === {4'b0000, stage2_A}));
    assert property (@(stage2_B or stage3_B) 1 |-> ##0 (stage3_B === {4'b0000, stage2_B}));

    // Upper bits of widened pipes remain zero
    assert property (@(stage3_A) 1 |-> ##0 (stage3_A[7:2] == '0));
    assert property (@(stage3_B) 1 |-> ##0 (stage3_B[7:2] == '0));

    // Functional decode mapping (only 4 coded outputs)
    assert property (@(stage3_A or Y) (stage3_A==8'd0) |-> ##0 (Y==16'h0001));
    assert property (@(stage3_A or Y) (stage3_A==8'd1) |-> ##0 (Y==16'h0002));
    assert property (@(stage3_A or Y) (stage3_A==8'd2) |-> ##0 (Y==16'h0004));
    assert property (@(stage3_A or Y) (stage3_A==8'd3) |-> ##0 (Y==16'h8000));

    // One-hot output invariant
    assert property (@(Y) 1 |-> ##0 $onehot(Y));

    // Direct functional check vs input A (B is not functionally used)
    assert property (@(A or Y) 1 |-> ##0 (A ? (Y==16'h0002) : (Y==16'h0001)));

    // B must not affect Y when A is stable
    assert property (@(A or B or Y) ($changed(B) && $stable(A)) |-> ##0 $stable(Y));

    // Known-ness: when inputs known, pipeline and output must be known
    assert property (@(A or B or Y or stage1_A or stage2_A or stage3_A)
                     (!$isunknown({A,B})) |-> ##0
                     !$isunknown({Y,stage1_A,stage1_B,stage2_A,stage2_B,stage3_A,stage3_B}));

    // Functional coverage
    cover property (@(A or Y) 1 |-> ##0 (A==1'b0 && Y==16'h0001));
    cover property (@(A or Y) 1 |-> ##0 (A==1'b1 && Y==16'h0002));

    cover property (@(stage3_A or Y) (stage3_A==8'd0) ##0 (Y==16'h0001));
    cover property (@(stage3_A or Y) (stage3_A==8'd1) ##0 (Y==16'h0002));
    cover property (@(stage3_A or Y) (stage3_A==8'd2) ##0 (Y==16'h0004));
    cover property (@(stage3_A or Y) (stage3_A==8'd3) ##0 (Y==16'h8000));

endmodule

bind decoder_4to16_pipeline decoder_4to16_pipeline_sva
(
    .A(A), .B(B), .Y(Y),
    .stage1_A(stage1_A), .stage1_B(stage1_B),
    .stage2_A(stage2_A), .stage2_B(stage2_B),
    .stage3_A(stage3_A), .stage3_B(stage3_B)
);

`endif