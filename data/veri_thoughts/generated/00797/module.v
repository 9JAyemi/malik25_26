
module Counter (
    input wire Clock,
    input wire Reset,
    input wire Enable,
    input wire [3:0] CountTo,
    output reg [3:0] CountValue,
    output reg CountFinished
);

    reg [3:0] nextCountValue;

    always @(*) begin
        if (CountValue == CountTo) begin
            CountFinished = 1;
            nextCountValue = 0;
        end else begin
            CountFinished = 0;
            nextCountValue = CountValue + 1;
        end
    end

    always @(posedge Clock) begin
        if (Reset) begin
            CountValue <= 0;
        end else if (Enable) begin
            CountValue <= nextCountValue;
        end
    end

endmodule