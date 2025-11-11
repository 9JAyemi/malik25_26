// SVA for shift_register
// Note: areset is active-low (per RTL sensitivity/logic)

module shift_register_sva (
    input  logic        clk,
    input  logic        areset,
    input  logic        load,
    input  logic        ena,
    input  logic [3:0]  data,
    input  logic [3:0]  q,
    input  logic [3:0]  q_next,
    input  logic [3:0]  reg1,
    input  logic [3:0]  reg2,
    input  logic [3:0]  reg3,
    input  logic [3:0]  reg4
);
    default clocking cb @(posedge clk); endclocking
    default disable iff (!areset)

    // Async reset clears immediately on negedge areset
    property p_async_reset_clears;
      @(negedge areset) ##0 (reg1=='0 && reg2=='0 && reg3=='0 && reg4=='0 && q=='0);
    endproperty
    assert property (p_async_reset_clears);

    // q_next wiring (width truncation implies q_next==reg1)
    assert property (q_next == reg1);

    // Hold when !ena (irrespective of load)
    assert property (!ena |=> $stable({reg1,reg2,reg3,reg4,q}));

    // Load behavior when ena
    assert property (ena && load |=> (reg1==$past(data) && reg2=='0 && reg3=='0 && reg4=='0 && q==$past(data)));

    // Shift behavior when ena && !load
    assert property (ena && !load |=> (reg1==$past(reg2) && reg2==$past(reg3) && reg3==$past(reg4) && reg4=='0 && q==$past(reg1)));

    // No X on observable outputs after reset release
    assert property (!$isunknown({q,q_next}));

    // Coverage
    cover property (@(negedge areset) 1);                       // async reset observed
    cover property ((ena && load) ##1 (ena && !load)[*3]);      // load then 3 shifts
    cover property ((!ena)[*2]);                                // hold for 2 cycles
    cover property ((ena && !load)[*4]);                        // sustained shifting
endmodule

// Bind to all instances of shift_register
bind shift_register shift_register_sva sva_i (
    .clk   (clk),
    .areset(areset),
    .load  (load),
    .ena   (ena),
    .data  (data),
    .q     (q),
    .q_next(q_next),
    .reg1  (reg1),
    .reg2  (reg2),
    .reg3  (reg3),
    .reg4  (reg4)
);