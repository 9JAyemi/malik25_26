```systemverilog
module mux_4to1_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic [1:0] SEL,
    input logic EN
);
    // Sequential logic: Mux output should be one of the inputs based on SEL and EN
    sequential_mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN == 1'b1) |-> (Y == (SEL == 2'b00 ? D0 : (SEL == 2'b01 ? D1 : (SEL == 2'b10 ? D2 : D3))))
    );

    // Combinational logic: Mux output should be one of the inputs based on SEL and EN
    combinational_mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN == 1'b0) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be disabled when EN is low
    disabled_mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (EN == 1'b0) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b11) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b10) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_3: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b01) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_4: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b00) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_5: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b11) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_6: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b10) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_7: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b01) |-> (Y == 1'b0)
    );

    // Sequential logic: Mux output should be stable when SEL is out of range
    out_of_range_mux_output_8: assert property (
        @(posedge CLK) disable iff (!RESETn) (SEL == 2'b00) |-> (Y == 1'b0)
    );
endmodule
```