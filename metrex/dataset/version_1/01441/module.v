module signalinput(
    input [1:0] testmode,
    input sysclk,
    output sigin1
);

reg [20:0] state;
reg [20:0] divide;
reg sigin;

assign sigin1 = sigin;

initial
begin
    sigin = 0;
    state = 21'b000000000000000000000;
    divide = 21'b0_0000_0111_1101_0000_0000;
end

always @(testmode)
begin
    case(testmode[1:0])
    2'b00: divide = 21'b0_0000_0111_1101_0000_0000;  // 3125Hz, divide by 32000
    2'b01: divide = 21'b0_0000_0011_1110_1000_0000;  // 250Hz, divide by 400000
    2'b10: divide = 21'b1_1110_1000_0100_1000_0000;  // 50Hz, divide by 2000000
    2'b11: divide = 21'b0_0000_0001_1111_0100_0000;  // 12500Hz, divide by 8000
    endcase
end

always @(posedge sysclk)
begin
    if(state == 0)
        sigin = ~sigin;
    state = state + 21'd2;
    if(state == divide)
        state = 0;
end

endmodule