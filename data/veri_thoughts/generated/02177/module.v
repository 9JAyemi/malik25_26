
module pwrgood_pp (
    output PG,
    input A,
    input VPWR,
    input KAGND
);

assign PG = (A && VPWR && KAGND);

endmodule
module power_good_checker (
    input A,
    input SLEEP_B,
    input VPWR,
    input KAGND,
    input VPB,
    input VNB,
    output X
);

// Local signals
wire pwrgood_pp0_out_A;
wire pwrgood_pp1_out_sleepb;

// Instantiate power good checkers
pwrgood_pp PG0 (
    .PG(pwrgood_pp0_out_A),
    .A(A),
    .VPWR(VPWR),
    .KAGND(KAGND)
);

pwrgood_pp PG1 (
    .PG(pwrgood_pp1_out_sleepb),
    .A(SLEEP_B),
    .VPWR(VPWR),
    .KAGND(KAGND)
);

// Combine power good signals
assign X = pwrgood_pp0_out_A && pwrgood_pp1_out_sleepb;

endmodule