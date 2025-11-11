module binary_counter (
    input clk,
    input reset,
    output reg [15:0] q,
    output reg [3:0] ov,
    output reg [3:1] ena
);

reg [3:0] count;

always @(posedge clk) begin
    if (reset) begin
        count <= 0;
        q <= 0;
        ov <= 0;
    end else begin
        if (ena[3]) begin
            count[3] <= ~count[3];
            if (count[3]) begin
                if (ena[2]) begin
                    count[2] <= ~count[2];
                    if (count[2]) begin
                        if (ena[1]) begin
                            count[1] <= ~count[1];
                            if (count[1]) begin
                                count[0] <= ~count[0];
                            end
                        end
                    end
                end
            end
        end
        q <= {count, 12'h0};
        ov <= count == 4'hF;
    end
end

endmodule

module overflow_counter (
    input [15:0] q,
    output reg [3:0] ov
);

always @(*) begin
    ov = q[15] + q[14] + q[13] + q[12];
end

endmodule