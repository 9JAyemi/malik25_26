module EXMEMreg_sva (
    input logic clk,
    input logic [4:0] Rtin,
    input logic [4:0] Rdin,
    input logic [31:0] PCplusin,
    input logic [31:0] ALUresultin,
    input logic [31:0] DatabusBin,
    input logic [1:0] RegDstin,
    input logic RegWrin,
    input logic MemWrin,
    input logic MemRdin,
    input logic [1:0] MemtoRegin,
    input logic [4:0] Rtout,
    input logic [4:0] Rdout,
    input logic [31:0] PCplusout,
    input logic [31:0] ALUresultout,
    input logic [31:0] DatabusBout,
    input logic [1:0] RegDstout,
    input logic RegWrout,
    input logic MemWrout,
    input logic MemRdout,
    input logic [1:0] MemtoRegout
);

    // Rtout captures Rtin on the previous rising edge.
    check_rtout_captures_rtin: assert property (
        @(posedge clk) 1'b1 |=> (Rtout == $past(Rtin))
    );

    // Rdout captures Rdin on the previous rising edge.
    check_rdout_captures_rdin: assert property (
        @(posedge clk) 1'b1 |=> (Rdout == $past(Rdin))
    );

    // PCplusout captures PCplusin on the previous rising edge.
    check_pcplusout_captures_pcplusin: assert property (
        @(posedge clk) 1'b1 |=> (PCplusout == $past(PCplusin))
    );

    // ALUresultout captures ALUresultin on the previous rising edge.
    check_aluresultout_captures_aluresultin: assert property (
        @(posedge clk) 1'b1 |=> (ALUresultout == $past(ALUresultin))
    );

    // DatabusBout captures DatabusBin on the previous rising edge.
    check_databusbout_captures_databusbin: assert property (
        @(posedge clk) 1'b1 |=> (DatabusBout == $past(DatabusBin))
    );

    // RegDstout captures RegDstin on the previous rising edge.
    check_regdstout_captures_regdstin: assert property (
        @(posedge clk) 1'b1 |=> (RegDstout == $past(RegDstin))
    );

    // RegWrout captures RegWrin on the previous rising edge.
    check_regwrout_captures_regwrin: assert property (
        @(posedge clk) 1'b1 |=> (RegWrout == $past(RegWrin))
    );

    // MemWrout captures MemWrin on the previous rising edge.
    check_memwrout_captures_memwrin: assert property (
        @(posedge clk) 1'b1 |=> (MemWrout == $past(MemWrin))
    );

    // MemRdout captures MemRdin on the previous rising edge.
    check_memrdout_captures_memrdin: assert property (
        @(posedge clk) 1'b1 |=> (MemRdout == $past(MemRdin))
    );

    // MemtoRegout captures MemtoRegin on the previous rising edge.
    check_memtoregout_captures_memtoregin: assert property (
        @(posedge clk) 1'b1 |=> (MemtoRegout == $past(MemtoRegin))
    );

endmodule