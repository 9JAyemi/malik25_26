
module digital_clock(
    input CLK,
    input RST,
    output reg [5:0] SEC,
    output reg [5:0] MIN,
    output reg [4:0] HOUR
);

    parameter SEC_CNT    = 60;
    parameter MIN_CNT    = 60;
    parameter HOUR_CNT   = 24;

    always @(posedge CLK) begin
        if (RST) begin
            SEC <= 6'b0;
            MIN <= 6'b0;
            HOUR <= 5'b0;
        end else begin
            if (SEC == (SEC_CNT - 1)) begin
                SEC <= 6'b0;
                if (MIN == (MIN_CNT - 1)) begin
                    MIN <= 6'b0;
                    if (HOUR == (HOUR_CNT - 1)) begin
                        HOUR <= 5'b0;
                    end else begin
                        HOUR <= HOUR + 1;
                    end
                end else begin
                    MIN <= MIN + 1;
                end
            end else begin
                SEC <= SEC + 1;
            end
        end
    end
    
endmodule