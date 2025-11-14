// SVA for multi_io_module (bind-ready). Focused, concise, high-quality checks + coverage.

module multi_io_module_sva (
  input clk,
  input reset,
  input [7:0] data_in,
  input       enable,
  input [3:0] addr,
  input [7:0] data_out,
  input       valid,
  input       done,
  input       error
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Core functional decode and data timing (1-cycle latency check)
  assert property ( enable |=> (
       data_out == $past(data_in)
    && ( $past(addr)==4'h0 -> ( valid && !done && !error))
    && ( $past(addr)==4'h1 -> ( valid && !done &&  error))
    && ( $past(addr)==4'h2 -> (!valid &&  done && !error))
    && ( $past(addr)==4'h3 -> (!valid &&  done &&  error))
    && ( $past(addr) inside {[4'h4:4'hF]} -> (!valid && !done && !error))
  )) else $error("Enable decode/data_out mismatch");

  // Outputs only change on prior enable or prior reset
  assert property ( $changed({data_out,valid,done,error})
                    |-> ($past(enable) || $past(reset)) )
    else $error("Outputs changed without prior enable/reset");

  // Hold when !enable (no assignments in DUT)
  assert property ( !enable |=> $stable({data_out,valid,done,error}) )
    else $error("Signals not stable while enable=0");

  // Mutual-exclusion and consistency of flags
  assert property ( !(valid && done) ) else $error("valid && done both 1");
  assert property ( error |-> (valid ^ done) ) else $error("error requires exactly one of valid/done");

  // No X/Z on outputs (outside reset)
  assert property ( !$isunknown({data_out,valid,done,error}) )
    else $error("X/Z detected on outputs");

  // Reset behavior (explicitly check across reset cycle)
  assert property (@(posedge clk) reset |=> (data_out==8'h00 && !valid && !done && !error))
    else $error("Reset did not clear outputs");

  // -----------------
  // Coverage
  // -----------------
  cover property (reset ##1 !reset); // reset release seen

  cover property ( enable && addr==4'h0 ##1 ( valid && !done && !error && data_out==$past(data_in)) );
  cover property ( enable && addr==4'h1 ##1 ( valid && !done &&  error && data_out==$past(data_in)) );
  cover property ( enable && addr==4'h2 ##1 (!valid &&  done && !error && data_out==$past(data_in)) );
  cover property ( enable && addr==4'h3 ##1 (!valid &&  done &&  error && data_out==$past(data_in)) );
  cover property ( enable && (addr inside {[4'h4:4'hF]}) ##1 (!valid && !done && !error && data_out==$past(data_in)) );

  cover property ( !enable ##1 (!enable && $stable({data_out,valid,done,error})) ); // hold window while disabled

endmodule

bind multi_io_module multi_io_module_sva sva_inst (.*);