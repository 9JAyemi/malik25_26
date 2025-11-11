module PhaseDelayMain(
    input clk,
    input decoderInput,
    output reg sigOut
);

parameter NUM_SIZE=7;
parameter SEQ_SIZE=NUM_SIZE+4;

reg [SEQ_SIZE-1:0] seq1,seq2,seq3,seq4;

integer i;

always @(posedge clk) begin
    // Shift the sequence to the right by one bit
    seq1 <= {seq1[0], seq1[SEQ_SIZE-1:1]};
    seq2 <= {seq2[0], seq2[SEQ_SIZE-1:1]};
    seq3 <= {seq3[0], seq3[SEQ_SIZE-1:1]};
    seq4 <= {seq4[0], seq4[SEQ_SIZE-1:1]};

    // Update the output signal based on the input binary sequence
    case ({seq1[NUM_SIZE-1], seq1[NUM_SIZE], seq1[NUM_SIZE+1], decoderInput})
        4'b0000: sigOut <= 1'b0; // No delay
        4'b0001: sigOut <= 1'b0; // No delay
        4'b0010: sigOut <= 1'b0; // No delay
        4'b0011: sigOut <= 1'b0; // No delay
        4'b0100: sigOut <= 1'b0; // No delay
        4'b0101: sigOut <= 1'b0; // No delay
        4'b0110: sigOut <= 1'b0; // No delay
        4'b0111: sigOut <= 1'b0; // No delay
        4'b1000: sigOut <= 1'b0; // No delay
        4'b1001: sigOut <= 1'b0; // No delay
        4'b1010: sigOut <= seq2[NUM_SIZE]; // 90 degrees delay
        4'b1011: sigOut <= seq2[NUM_SIZE+1]; // 90 degrees delay
        4'b1100: sigOut <= seq3[NUM_SIZE]; // 180 degrees delay
        4'b1101: sigOut <= seq3[NUM_SIZE+1]; // 180 degrees delay
        4'b1110: sigOut <= seq4[NUM_SIZE]; // 270 degrees delay
        4'b1111: sigOut <= seq4[NUM_SIZE+1]; // 270 degrees delay
    endcase
end

// Initialize the binary sequences
initial begin
    seq1 = 11'b01000000000; // In phase
    seq2 = 11'b01001000000; // 90 degrees out of phase
    seq3 = 11'b01010000000; // 180 degrees out of phase
    seq4 = 11'b01011000000; // 270 degrees out of phase
end

endmodule