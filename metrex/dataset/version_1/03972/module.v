module waveform_generator (
    input wire X,
    output reg [31:0] waveform
);

integer time;

initial begin
    waveform = 0;
    time = 0;
end

always @(posedge X) begin
    waveform[time] = X;
    time = time + 1;
end

endmodule