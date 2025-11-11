


module functionGen #(
    parameter ARCH                = "GENERIC", parameter BIT_COMPRESS_PHASE  = 1,         parameter BIT_COMPRESS_OUTPUT = 1,         parameter OUT_WIDTH           = 16,        parameter FREQ_WIDTH          = 16,        parameter INCLUDE_CLAMP       = 1          )
(
    input clk,                          input rst,                          input en,                           input [1:0] waveType,               input [FREQ_WIDTH-1:0] freq,        input [FREQ_WIDTH-1:0] phaseOffset, input [OUT_WIDTH-1:0] offset,       input [OUT_WIDTH-1:0] amplitude,    output signed [OUT_WIDTH-1:0] outSignal
);

initial begin
    if (ARCH != "GENERIC" && ARCH != "XIL_7SERIES" && ARCH != "XIL_SPARTAN6") begin
        $display("Attribute ARCH on functionGen instance %m is set to %s. Valid values are GENERIC, XIL_7SERIES, and XIL_SPARTAN6.", ARCH);
        #1 $finish;
    end
    if (BIT_COMPRESS_PHASE != 0 && BIT_COMPRESS_PHASE != 1) begin
        $display("Attribute BIT_COMPRESS_PHASE on functionGen instance %m is set to %d. Valid values are 0 and 1.", BIT_COMPRESS_PHASE);
        #1 $finish;
    end
    if (BIT_COMPRESS_OUTPUT != 0 && BIT_COMPRESS_OUTPUT != 1) begin
        $display("Attribute BIT_COMPRESS_OUTPUT on functionGen instance %m is set to %d. Valid values are 0 and 1.", BIT_COMPRESS_OUTPUT);
        #1 $finish;
    end
    if (OUT_WIDTH < 3) begin
        $display("Attribute OUT_WIDTH on functionGen instance %m is set to %d. Must be at least 3.", OUT_WIDTH);
        #1 $finish;
    end
    if (FREQ_WIDTH < 4) begin
        $display("Attribute FREQ_WIDTH on functionGen instance %m is set to %d. Must be at least 4.", FREQ_WIDTH);
        #1 $finish;
    end
    if (INCLUDE_CLAMP != 0 && INCLUDE_CLAMP != 1) begin
        $display("Attribute INCLUDE_CLAMP on functionGen instance %m is set to %d. Valid values are 0 and 1.", INCLUDE_CLAMP);
        #1 $finish;
    end
end

localparam WAVE_SINE     = 0;
localparam WAVE_TRIANGLE = 1;
localparam WAVE_SQUARE   = 2;
localparam WAVE_SAWTOOTH = 3;

localparam LOCAL_WIDTH = 18; localparam ANGLE_WIDTH = 10;
localparam SINE_WIDTH = 18;

localparam TABLE_LEN = 2**(ANGLE_WIDTH);
localparam WIDE_WIDTH = OUT_WIDTH+LOCAL_WIDTH;

wire [FREQ_WIDTH-3:0] xorPhase;
wire [ANGLE_WIDTH-1:0] xorSdPhase;

reg signed [LOCAL_WIDTH-1:0] sineOrTriangle;
reg signed [WIDE_WIDTH+1:0] wideSignalWord;
reg signed [LOCAL_WIDTH-1:0] unscaledSignal;
reg signed [OUT_WIDTH-1:0] clampedSignal;

reg [ANGLE_WIDTH+1:0] sdPhase;
reg [FREQ_WIDTH-1:0] phaseAcc;
reg [FREQ_WIDTH-1:0] phase;
reg [SINE_WIDTH-1:0] sineTable [TABLE_LEN-1:0];
reg [SINE_WIDTH-1:0] halfSine;
reg [LOCAL_WIDTH-2:0] halfSineOrTriangle;
reg signBit;
reg signBitD1;

integer i;

always @(posedge clk) begin
    if (rst) begin
        phase          <= 'd0;
        phaseAcc       <= 'd0;
        wideSignalWord <= 'd0;
        unscaledSignal <= 'd0;
    end
    else if (en) begin
        phaseAcc       <= phaseAcc + freq;
        phase          <= phaseAcc + phaseOffset;

        case (waveType)
            WAVE_SINE     : unscaledSignal <= sineOrTriangle;
            WAVE_TRIANGLE : unscaledSignal <= sineOrTriangle;
            WAVE_SQUARE   : unscaledSignal <= {phase[FREQ_WIDTH-1], {(LOCAL_WIDTH-2){~phase[FREQ_WIDTH-1]}}, 1'b1};
            WAVE_SAWTOOTH : begin
                if (FREQ_WIDTH >= LOCAL_WIDTH) begin
                    unscaledSignal <= $signed(phase) >>> (FREQ_WIDTH-LOCAL_WIDTH);
                end
                else begin
                    unscaledSignal <= $signed(phase) <<< (LOCAL_WIDTH-FREQ_WIDTH);
                end
            end
        endcase

        if (BIT_COMPRESS_OUTPUT) begin
            wideSignalWord <= unscaledSignal * $signed({1'b0, amplitude}) 
                            + $signed({offset, wideSignalWord[LOCAL_WIDTH-1:0]});
        end
        else begin
            wideSignalWord <= unscaledSignal * $signed({1'b0, amplitude}) 
                            + $signed({offset, {LOCAL_WIDTH{1'b0}}});
        end

        clampedSignal  <= !(&wideSignalWord[WIDE_WIDTH+1-:3] | ~|wideSignalWord[WIDE_WIDTH+1-:3])
                        ? {wideSignalWord[WIDE_WIDTH+1], {(OUT_WIDTH-1){~wideSignalWord[WIDE_WIDTH+1]}}}
                        :  wideSignalWord[WIDE_WIDTH-1-:OUT_WIDTH];

    end
end

if (INCLUDE_CLAMP) begin
    assign outSignal = clampedSignal;
end
else begin
    assign outSignal = wideSignalWord[WIDE_WIDTH-1-:OUT_WIDTH];
end

if (ANGLE_WIDTH+2 >= FREQ_WIDTH) begin
    always @(phase) begin
        sdPhase = phase << (ANGLE_WIDTH+2-FREQ_WIDTH);
    end
end
else if (BIT_COMPRESS_PHASE) begin
    reg [(FREQ_WIDTH-ANGLE_WIDTH-3):0] sdPhaseAcc;
    always @(posedge clk) begin
        if (rst) begin
            sdPhase <= 'd0;
            sdPhaseAcc <= 'd0;
        end
        else begin
            {sdPhase,sdPhaseAcc} <= phase + sdPhaseAcc;
        end
    end
end
else begin
    always @(phase) begin
        sdPhase = phase >> (FREQ_WIDTH-ANGLE_WIDTH-2);
    end
end


assign xorPhase = (phase[FREQ_WIDTH-2]) ? ~phase[FREQ_WIDTH-3:0] : phase[FREQ_WIDTH-3:0];

if (BIT_COMPRESS_PHASE) begin
    assign xorSdPhase = (sdPhase[ANGLE_WIDTH]) ? ~sdPhase[ANGLE_WIDTH-1:0] : sdPhase[ANGLE_WIDTH-1:0];
end
else begin
    if (ANGLE_WIDTH+2 >= FREQ_WIDTH) begin
        assign xorSdPhase = xorPhase << (ANGLE_WIDTH+2-FREQ_WIDTH);
    end
    else begin
        assign xorSdPhase = xorPhase >> (FREQ_WIDTH-ANGLE_WIDTH-2);
    end
end

initial begin
    signBit            = 1'b0;
    signBitD1          = 1'b0;
    halfSine           = 'd0;
    halfSineOrTriangle = 'd0;
    sineOrTriangle     = 'd0;
    for(i=0; i<TABLE_LEN; i=i+1) begin
        sineTable[i] = $rtoi($floor($sin((i+0.5)*3.14159265358979/(TABLE_LEN*2))*(2**SINE_WIDTH-1)+0.5));
    end
end

always @(posedge clk) begin
    if (en) begin
        signBit    <= sdPhase[ANGLE_WIDTH+1];
        signBitD1  <= signBit;
        halfSine <= sineTable[xorSdPhase];
        if ((SINE_WIDTH > LOCAL_WIDTH-1) && (FREQ_WIDTH > LOCAL_WIDTH)) begin
            halfSineOrTriangle <= (waveType[0]) ? {xorPhase,1'b1} >> (FREQ_WIDTH-LOCAL_WIDTH) : halfSine >> (SINE_WIDTH-LOCAL_WIDTH+1);
        end 
        else if ((SINE_WIDTH > LOCAL_WIDTH-1) && (FREQ_WIDTH <= LOCAL_WIDTH)) begin
            halfSineOrTriangle <= (waveType[0]) ? {xorPhase,1'b1} << (LOCAL_WIDTH-FREQ_WIDTH) : halfSine >> (SINE_WIDTH-LOCAL_WIDTH+1);
        end 
        else if ((SINE_WIDTH <= LOCAL_WIDTH-1) && (FREQ_WIDTH > LOCAL_WIDTH)) begin
            halfSineOrTriangle <= (waveType[0]) ? {xorPhase,1'b1} >> (FREQ_WIDTH-LOCAL_WIDTH) : halfSine << (LOCAL_WIDTH-1-SINE_WIDTH);
        end 
        else begin
            halfSineOrTriangle <= (waveType[0]) ? {xorPhase,1'b1} << (LOCAL_WIDTH-FREQ_WIDTH) : halfSine << (LOCAL_WIDTH-1-SINE_WIDTH);
        end 
        sineOrTriangle <= $signed({LOCAL_WIDTH{signBitD1}} ^ {1'b0, halfSineOrTriangle}) + $signed({1'b0, signBitD1});
    end
end
endmodule
