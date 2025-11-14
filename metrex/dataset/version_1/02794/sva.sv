// SVA for pwmregister. Bind this to the DUT.
module pwmregister_sva #(parameter WIDTH=8) (
  input logic                clk,
  input logic                pwmldce,
  input logic [WIDTH-1:0]    wrtdata,
  input logic [WIDTH-1:0]    pwmval
);
  // Enable $past after first clock
  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Core functional checks
  // 1) Register updates with previous cycle's data when enabled
  assert property (pwmldce |=> pwmval == $past(wrtdata))
    else $error("pwmval did not load wrtdata on enable");

  // 2) Register holds value when not enabled
  assert property (!pwmldce |=> pwmval == $past(pwmval))
    else $error("pwmval changed without enable low->hold violation");

  // 3) Any change on pwmval must be caused by enable in prior cycle
  assert property ($changed(pwmval) |-> $past(pwmldce))
    else $error("pwmval changed without prior enable");

  // 4) Do not load unknown data (X/Z) when enabling
  assert property (pwmldce |-> !$isunknown(wrtdata))
    else $error("wrtdata has X/Z while pwmldce is asserted");

  // 5) Loaded value must be known if loaded data was known
  assert property ($past(pwmldce) && !$isunknown($past(wrtdata)) |-> !$isunknown(pwmval))
    else $error("pwmval became X/Z after a valid load");

  // Coverage
  cover property (pwmldce ##1 pwmval == $past(wrtdata));                  // basic load
  cover property (pwmldce [*2]);                                          // back-to-back loads
  cover property (!pwmldce [*3]);                                         // multi-cycle hold
  cover property (pwmldce && wrtdata == '0);                              // load all zeros
  cover property (pwmldce && wrtdata == {WIDTH{1'b1}});                   // load all ones
  cover property (!pwmldce ##1 $changed(wrtdata));                        // data toggles while disabled
endmodule

// Bind into the DUT (uncomment in TB or a bind file)
// bind pwmregister pwmregister_sva #(.WIDTH(8))) pwmregister_sva_i (.*);