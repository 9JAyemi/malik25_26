
module clock_divider_sim #(
    parameter DIVISOR = 2
) (
    input wire CLK,
    output reg CLOCK
);

integer cnt;
initial cnt = 0;

wire [31:0] DIV;
assign DIV = DIVISOR;

always @(posedge CLK)
    if(cnt == DIVISOR -1)
        cnt <= 0;
    else
        cnt <= cnt + 1;

initial CLOCK = 0;

always @(posedge CLK) begin
    if (DIVISOR % 2 == 0) begin
        if(cnt == DIVISOR/2-1) // posedge
            CLOCK <= ~CLOCK;
    end else begin
        if(cnt == DIVISOR/2 && DIV[0] == 1) // posedge
            CLOCK <= ~CLOCK;
    end

    if(cnt == DIVISOR-1) // posedge
        CLOCK <= ~CLOCK;
end

endmodule