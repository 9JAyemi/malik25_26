module sm_clk_divider
#(
    parameter shift  = 16,
              bypass = 0
)
(
    input           clkIn,
    input           rst_n,
    input   [ 3:0 ] devide,
    input           enable,
    output          clkOut
);
    wire [31:0] cntr;
    wire [31:0] cntrNext = cntr + 1;
    sm_register_we r_cntr(clkIn, rst_n, enable, cntrNext, cntr);

    assign clkOut = bypass ? clkIn 
                           : cntr[shift + devide];
endmodule

module sm_register_we
(
    input clk,
    input reset_n,
    input we,
    input [31:0] d,
    output reg [31:0] q
);

    always @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            q <= 0;
        end else if (we) begin
            q <= d;
        end
    end

endmodule