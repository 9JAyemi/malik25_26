
module clk_generator(
    input clk,
    input clk_ena,
    input rstn,
    output reg clk_out
);

parameter BAUDRATE = 8;
parameter M2 = 4;

localparam COUNTER_WIDTH = $clog2(BAUDRATE);

reg [COUNTER_WIDTH-1:0] divcounter = 0;

// Counter
always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        divcounter <= 0;
    end
    else if (clk_ena) begin
        divcounter <= (divcounter == BAUDRATE - 1) ? 0 : divcounter + 1;
    end
    else begin
        divcounter <= BAUDRATE - 1;
    end
end

// Output
always @(posedge clk) begin
    clk_out <= (divcounter == M2) ? clk_ena : 0;
end

endmodule
