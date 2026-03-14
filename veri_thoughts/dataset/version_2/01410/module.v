
module clock_gate (
    input clk,
    input en,
    input te,
    output reg enclk
);

    TLATNTSCAX2TS latch (
        .E(en),
        .SE(te),
        .CK(clk),
        .ECK(enclk)
    );

endmodule
module TLATNTSCAX2TS (
    input E,
    input SE,
    input CK,
    output reg ECK
);

always @(posedge CK) begin
    if (E) begin
        ECK <= SE;
    end else begin
        ECK <= ECK; // Hold the previous value
    end
end

endmodule