// SVA for top_module
// Focused, concise checks + targeted coverage
module top_module_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [3:0]  sync_counter,
    input  logic [3:0]  async_counter,
    input  logic [2:0]  pattern_counter,
    input  logic [2:0]  pattern,
    input  logic        led
);
    default clocking cb @(posedge clk); endclocking

    // Basic sanity
    assert property (cb !$isunknown({reset,sync_counter,async_counter,pattern_counter,pattern,led}));

    // Synchronous reset drives exact values
    assert property (cb reset |-> (sync_counter==0 && async_counter==0 &&
                                   pattern_counter==0 && pattern==3'b001 && led==0));

    // sync_counter: 0..10 then wrap to 0
    assert property (cb disable iff (reset) sync_counter <= 10);
    assert property (cb $past(!reset) && $past(sync_counter)<=9  |-> sync_counter == $past(sync_counter)+1);
    assert property (cb $past(!reset) && $past(sync_counter)==10 |-> sync_counter == 0);

    // async_counter: increments modulo 16 (wrap-by-width)
    assert property (cb $past(!reset) |-> async_counter == $past(async_counter)+1);

    // pattern_counter: increments modulo 8 (wrap-by-width)
    assert property (cb $past(!reset) |-> pattern_counter == $past(pattern_counter)+1);

    // pattern legal encodings only
    assert property (cb disable iff (reset) pattern inside {3'b001,3'b010,3'b011,3'b100});

    // pattern changes only on coded update condition; when it does, transition is correct
    assert property (cb disable iff (reset)
        (pattern != $past(pattern)) |-> $past(pattern_counter)==3'd10);
    assert property (cb disable iff (reset)
        $past(pattern_counter)==3'd10 |-> pattern == (($past(pattern)==3'b100) ? 3'b001
                                                                                : ($past(pattern)+1)));

    // LED behavior matches case statement
    assert property (cb disable iff (reset) (pattern==3'b001) |-> led == (sync_counter < 3));
    assert property (cb disable iff (reset) (pattern==3'b010) |-> led == (sync_counter < 2));
    assert property (cb disable iff (reset) (pattern==3'b011) |-> led == (sync_counter < 2));
    assert property (cb disable iff (reset) (pattern==3'b100) |-> led == 1'b0);

    // Targeted coverage
    cover property (cb disable iff (reset) sync_counter==10 ##1 sync_counter==0);
    cover property (cb disable iff (reset) async_counter==4'hF ##1 async_counter==4'h0);
    // Expected LED pulse shape for pattern 001
    cover property (cb disable iff (reset)
        pattern==3'b001 && sync_counter==0 && led ##1
        pattern==3'b001 && sync_counter==1 && led ##1
        pattern==3'b001 && sync_counter==2 && led ##1
        pattern==3'b001 && sync_counter==3 && !led);
    // Intended pattern rotation (will highlight if never reached)
    cover property (cb disable iff (reset)
        pattern==3'b001 ##[1:$] pattern==3'b010 ##[1:$]
        pattern==3'b011 ##[1:$] pattern==3'b100 ##[1:$] pattern==3'b001);
endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (
    .clk            (clk),
    .reset          (reset),
    .sync_counter   (sync_counter),
    .async_counter  (async_counter),
    .pattern_counter(pattern_counter),
    .pattern        (pattern),
    .led            (led)
);