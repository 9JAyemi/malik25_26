
module clock_generator (
    input clk,
    output reg genclk
);

    reg [7:0] cyc;
    initial cyc = 0;
    wire genthiscyc = ( (cyc % 2) == 1 );
    
    always @ (posedge clk) begin
        cyc <= cyc + 8'h1;
        if (cyc < 8'h80) genclk <= genthiscyc;
        if (cyc >= 8'h80) genclk <= ~genclk;
    end
    
endmodule