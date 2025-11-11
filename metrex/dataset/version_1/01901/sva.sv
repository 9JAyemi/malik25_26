// SVA for module accu
module accu_sva
(
    input logic               clk,
    input logic               rst_n,
    input logic [7:0]         data_in,
    input logic               control,
    input logic               ready_b,
    input logic               ready_a,
    input logic               valid_b,
    input logic [7:0]         data_out,
    input logic [7:0]         accumulator,
    input logic [2:0]         counter
);

default clocking cb @(posedge clk); endclocking
default disable iff (!rst_n);

// Reset behavior
assert property (cb !rst_n |-> (accumulator==8'h00 && counter==3'h0 && valid_b==1'b0));

// Ready relationship
assert property (cb ready_a == ~ready_b);

// No-control holds state and clears valid
assert property (cb !control |=> ($stable(accumulator) && $stable(counter) && valid_b==1'b0));

// Accumulate/XOR and count on control when not wrapping
assert property (cb control && (counter != 3'h7)
                 |=> (accumulator == $past(accumulator) ^ $past(data_in)) &&
                     (counter     == $past(counter)+3'h1) &&
                     (valid_b     == 1'b0));

// Wrap behavior on 8th control: output previous accumulator, clear acc/cnt, raise valid
assert property (cb control && (counter == 3'h7)
                 |=> (data_out   == $past(accumulator)) &&
                     (accumulator == 8'h00) &&
                     (counter     == 3'h0) &&
                     (valid_b     == 1'b1));

// Data_out only updates on wrap
assert property (cb !(control && counter==3'h7) |=> $stable(data_out));

// valid_b only when prior cycle was wrap, and is a 1-cycle pulse
assert property (cb valid_b |-> ($past(control) && $past(counter)==3'h7));
assert property (cb valid_b |=> !valid_b);

// Coverage

// See at least one wrap event
cover property (cb control && counter==3'h7);

// See 8 consecutive control cycles leading to a wrap (valid next cycle)
cover property (cb control[*8] ##1 valid_b);

// Two wraps separated by some idle cycles
cover property (cb (control && counter==3'h7) ##1 !control[*3] ##1 (control && counter==3'h7));

// Exercise ready inversion both ways
cover property (cb ready_b ##1 !ready_b ##1 ready_b);

endmodule

// Bind into all accu instances
bind accu accu_sva i_accu_sva (.*);