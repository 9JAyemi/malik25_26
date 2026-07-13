module oh_mux4_sva (
    input logic sel3,
    input logic sel2,
    input logic sel1,
    input logic sel0,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    output logic [DW-1:0] out
);
    parameter DW = 1;

    // Sequential logic: Mux output is determined by the selection signals
    // Mux output should be one of the input signals based on the selection
    mux_output: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        (sel0 | sel1 | sel2 | sel3) |-> 
        (out == ({(DW){sel0}} & in0[DW-1:0] |
                  {(DW){sel1}} & in1[DW-1:0] |
                  {(DW){sel2}} & in2[DW-1:0] |
                  {(DW){sel3}} & in3[DW-1:0]))
    );

    // Combinational logic: Error detection when more than one selection signal is high
    // Error should be asserted when more than one selection signal is high
    error_detection: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        (sel0 | sel1 | sel2 | sel3) & 
        ~(sel0 ^ sel1 ^ sel2 ^ sel3) |-> 
        error
    );

    // Combinational logic: Error signal should be asserted when more than one selection signal is high
    // Error signal should be deasserted when only one selection signal is high
    error_signal: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        (sel0 | sel1 | sel2 | sel3) & 
        (sel0 ^ sel1 ^ sel2 ^ sel3) |-> 
        !error
    );

    // Combinational logic: Error signal should be deasserted when no selection signal is high
    // Error signal should be deasserted when no selection signal is high
    error_no_selection: assert property (
        @(posedge CLK) disable iff (!RESETn) 
        ~(sel0 | sel1 | sel2 | sel3) |-> 
        !error
    );
endmodule