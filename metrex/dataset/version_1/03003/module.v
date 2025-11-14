
module relojes (
    input wire CLK_IN1,
    // Clock out ports
    output wire CLK_OUT1,
    output wire CLK_OUT2,
    output wire CLK_OUT3,
    output wire CLK_OUT4
);

    // Internal registers and wires
    reg [7:0] count1;
    reg [7:0] count2;
    reg [7:0] count3;
    reg [7:0] count4;

    // Clock division logic
    always @(posedge CLK_IN1) begin
        count1 <= count1 + 1;
        if (count1 == 8'd24) begin
            count1 <= 0;
            count2 <= count2 + 1;
        end
        if (count2 == 8'd12) begin
            count2 <= 0;
            count3 <= count3 + 1;
        end
        if (count3 == 8'd6) begin
            count3 <= 0;
            count4 <= count4 + 1;
        end
    end

    // Clock outputs
    assign CLK_OUT1 = count1[0];
    assign CLK_OUT2 = count2[0];
    assign CLK_OUT3 = count3[0];
    assign CLK_OUT4 = count4[0];

endmodule
