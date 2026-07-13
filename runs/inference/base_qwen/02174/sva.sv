module zet_bitlog_sva (
    input logic [15:0] x,
    output logic [15:0] o,
    output logic cfo,
    output logic ofo
);
    // Combinational logic: o is the bitwise NOT of x
    comb_logic_1: assert property (
        @(posedge clk) disable iff (!RESETn) (o == ~x)
    );
    // Combinational logic: cfo is always 0
    comb_logic_2: assert property (
        @(posedge clk) disable iff (!RESETn) (cfo == 1'b0)
    );
    // Combinational logic: ofo is always 0
    comb_logic_3: assert property (
        @(posedge clk) disable iff (!RESETn) (ofo == 1'b0)
    );
endmodule