
module sqrt_16bit (
    input [15:0] a,
    input ctrl,
    output reg [15:0] b
);

    reg [15:0] x;
    reg [3:0] i;
    reg [15:0] temp;

    always @(*) begin
        x = 8'd0;
        i = 4'd0;
        temp = 16'd0;
        for (i = 4'd0; i < 4'd8; i = i + 1) begin
            temp = (x << 1) + (1 << (7 - i));
            if (temp * temp <= a) begin
                x = temp;
            end
        end
        if (ctrl == 1) begin
            if (((x + 1) * (x + 1) - a) <= (a - x * x)) begin
                b = x + 1;
            end else begin
                b = x;
            end
        end else begin
            b = x;
        end
    end

endmodule