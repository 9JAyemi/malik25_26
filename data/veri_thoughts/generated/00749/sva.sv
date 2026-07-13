module Problem2_sva (
    input logic clk,
    input logic [7:0] Input,
    input logic Ein,
    input logic Eout,
    input logic GS,
    input logic [2:0] Number
);
    // When disabled, outputs and Number are zero.
    check_disabled_defaults: assert property (
        @(posedge clk) (Ein == 1'b0) |-> ((Eout == 1'b0) && (GS == 1'b0) && (Number == 3'b000))
    );

    // When enabled with no inputs set, Eout=1, GS=0, Number=0.
    check_enabled_no_input: assert property (
        @(posedge clk) (Ein && (Input == 8'b0)) |-> ((GS == 1'b0) && (Eout == 1'b1) && (Number == 3'b000))
    );

    // When enabled with any input set, GS=1 and Eout=0.
    check_enabled_some_input: assert property (
        @(posedge clk) (Ein && (Input != 8'b0)) |-> ((GS == 1'b1) && (Eout == 1'b0))
    );

    // GS equals Ein AND (any Input bit set).
    check_gs_definition: assert property (
        @(posedge clk) GS == (Ein && (Input != 8'b0))
    );

    // Eout equals Ein AND (no Input bits set).
    check_eout_definition: assert property (
        @(posedge clk) Eout == (Ein && (Input == 8'b0))
    );

    // When enabled, Eout and GS are complements.
    check_eout_gs_complement_when_enabled: assert property (
        @(posedge clk) Ein |-> (Eout == ~GS)
    );

    // Priority encoding: if Input[7]==1 when enabled, Number=7.
    check_prio7: assert property (
        @(posedge clk) (Ein && Input[7]) |-> (Number == 3'b111)
    );

    // Priority encoding: else if Input[6]==1 with no higher bit, Number=6.
    check_prio6: assert property (
        @(posedge clk) (Ein && !Input[7] && Input[6]) |-> (Number == 3'b110)
    );

    // Priority encoding: else if Input[5]==1 with no higher bits, Number=5.
    check_prio5: assert property (
        @(posedge clk) (Ein && !Input[7] && !Input[6] && Input[5]) |-> (Number == 3'b101)
    );

    // Priority encoding: else if Input[4]==1 with no higher bits, Number=4.
    check_prio4: assert property (
        @(posedge clk) (Ein && !Input[7] && !Input[6] && !Input[5] && Input[4]) |-> (Number == 3'b100)
    );

    // Priority encoding: else if Input[3]==1 with no higher bits, Number=3.
    check_prio3: assert property (
        @(posedge clk) (Ein && !Input[7] && !Input[6] && !Input[5] && !Input[4] && Input[3]) |-> (Number == 3'b011)
    );

    // Priority encoding: else if Input[2]==1 with no higher bits, Number=2.
    check_prio2: assert property (
        @(posedge clk) (Ein && !Input[7] && !Input[6] && !Input[5] && !Input[4] && !Input[3] && Input[2]) |-> (Number == 3'b010)
    );

    // Priority encoding: else if Input[1]==1 with no higher bits, Number=1.
    check_prio1: assert property (
        @(posedge clk) (Ein && !Input[7] && !Input[6] && !Input[5] && !Input[4] && !Input[3] && !Input[2] && Input[1]) |-> (Number == 3'b001)
    );

    // Priority encoding: else if only Input[0]==1, Number=0.
    check_prio0: assert property (
        @(posedge clk) (Ein && !(|Input[7:1]) && Input[0]) |-> (Number == 3'b000)
    );

    // Eout and GS are never both HIGH.
    check_gs_eout_mutex: assert property (
        @(posedge clk) !(GS && Eout)
    );
endmodule