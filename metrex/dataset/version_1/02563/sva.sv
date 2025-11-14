// SVA for longest_sequence_detection
// Bind into the DUT to observe internals

module longest_sequence_detection_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] data,
  input  logic [3:0]  count,
  input  logic [3:0]  max_count,
  input  logic [3:0]  index,
  input  logic [3:0]  max_index,
  input  logic [3:0]  length,
  input  logic [3:0]  start_index
);
  default clocking cb @(posedge clk); endclocking

  // Helpers
  wire all1   = (data == 16'hFFFF);
  wire all0   = (data == 16'h0000);
  wire normal = !(all1 || all0);

  // Basic reset behavior
  assert property (reset |=> count==0 && max_count==0 && index==0 && max_index==0 && length==0 && start_index==0);

  // Outputs mirror internal state
  assert property (length == max_count);
  assert property (start_index == max_index);

  // Special cases
  assert property (disable iff (reset) all0 |=> count==0 && max_count==0 && index==0 && max_index==0);

  // Intent check: all-ones should saturate to 15 and start at 0 (will flag width/overflow issues)
  assert property (disable iff (reset) all1 |=> count==4'd15 && max_count==4'd15 && index==0 && max_index==0
                                         && length==4'd15 && start_index==0);

  // Normal-case: on a '1' bit, count increments; index holds unless starting new run
  assert property (disable iff (reset)
    normal && data[0]
    |=>  count == $past(count,1,reset) + 1
      && ( ($past(count,1,reset)==0) ? (index==0) : (index==$past(index,1,reset)) )
      && max_count == $past(max_count,1,reset)
      && max_index == $past(max_index,1,reset)
  );

  // Normal-case: on a '0' bit with no new max, push index and clear count; keep max
  assert property (disable iff (reset)
    normal && !data[0] && ($past(count,1,reset) <= $past(max_count,1,reset))
    |=>  max_count == $past(max_count,1,reset)
      && max_index == $past(max_index,1,reset)
      && count == 0
      && index == $past(index,1,reset) + $past(count,1,reset) + 1
  );

  // Normal-case: on a '0' bit with new max, update max and push index; clear count
  assert property (disable iff (reset)
    normal && !data[0] && ($past(count,1,reset) > $past(max_count,1,reset))
    |=>  max_count == $past(count,1,reset)
      && max_index == $past(index,1,reset)
      && count == 0
      && index == $past(index,1,reset) + $past(count,1,reset) + 1
  );

  // Safety: in normal operation, max_count never decreases
  assert property (disable iff (reset) normal |=> max_count >= $past(max_count,1,reset));

  // Coverage
  cover property (all0);
  cover property (all1);
  cover property (disable iff (reset) normal && data[0]);                         // counting a '1'
  cover property (disable iff (reset) normal && !data[0] && $past(count,1,reset)>$past(max_count,1,reset)); // new max update
  cover property (disable iff (reset) normal && !data[0] && $past(count,1,reset)<= $past(max_count,1,reset)); // no-update on tie/shorter
  // Potential overflow attempt (wrap hazard) on increment
  cover property (disable iff (reset) normal && data[0] && $past(count,1,reset)==4'hF);

endmodule

bind longest_sequence_detection longest_sequence_detection_sva sva_i (
  .clk(clk),
  .reset(reset),
  .data(data),
  .count(count),
  .max_count(max_count),
  .index(index),
  .max_index(max_index),
  .length(length),
  .start_index(start_index)
);