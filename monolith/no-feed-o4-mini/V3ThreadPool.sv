module Ctor #(parameter int N = 2) (input logic enable, output logic oneThread, output int threadCount);
  always_comb begin
    threadCount = (N >= 1) ? N : 1;
    oneThread = (threadCount == 1);
  end
  generate
    if (N > 1) begin : workers
      genvar i;
      for (i = 0; i < N; i = i + 1) begin : spawn_thread
      end
    end
  endgenerate
endmodule
module Dtor (input logic shutdownReq, output logic shutdownDone);
  event ev;
  always_ff @(posedge shutdownReq) begin
    -> ev;
    shutdownDone <= 1;
  end
endmodule
module Enqueue #(int QSIZE = 4) (input logic clk, input logic enqueue, input int dataIn, output logic processed);
  mailbox #(.WIDTH(32), .SIZE(QSIZE)) mbx;
  int pendingJobs;
  event notifyEv;
  always_ff @(posedge clk) begin
    if (enqueue) begin
      if (mbx.num() == 0) begin
        processed <= 1;
      end else begin
        mbx.put(dataIn);
        pendingJobs <= pendingJobs + 1;
        -> notifyEv;
        processed <= 0;
      end
    end
  end
endmodule
module Wait (input logic clk, input logic shutdown, input logic [31:0] pendingJobs, output logic waiting);
  always_ff @(posedge clk) begin
    if (pendingJobs > 0 && !shutdown)
      waiting <= 1;
    else
      waiting <= 0;
  end
  always_ff @(posedge clk) begin
    if (shutdown) begin
    end
  end
endmodule
module StartWorker (input logic trigger, output logic loopEntry);
  always_comb begin
    loopEntry = trigger;
  end
endmodule
module WorkerJobLoop (input logic clk, input logic shutdown, input logic queueEmpty, output logic jobTaken, output logic jobDone);
  mailbox #(.WIDTH(32), .SIZE(8)) mbx;
  always_ff @(posedge clk) begin
    if (!shutdown) begin
      if (!queueEmpty) begin
        int job;
        mbx.get(job);
        jobTaken <= 1;
        jobDone <= 1;
      end
    end
  end
endmodule
module SelfTestMtDisabled (input logic dummyIn, output logic dummyOut);
  always_comb dummyOut = dummyIn;
endmodule
module SelfTest (input logic clk, input logic reset, output logic [15:0] result);
  class Mutex;
    semaphore sem;
    function new();
      sem = new(1);
    endfunction
    function void lock();
      sem.get();
    endfunction
    function void unlock();
      sem.put(1);
    endfunction
  endclass
  Mutex commonMutex;
  int commonValue;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      commonValue <= 0;
    end else begin
      commonMutex.lock();
      commonValue <= commonValue + 1;
      commonMutex.unlock();
    end
  end
  assign result = commonValue;
endmodule
module ThreadScope_Ctor (input logic init, output logic inScope);
  always_ff @(posedge init) begin
    inScope <= init;
  end
endmodule
module ThreadScope_Enqueue #(int S = 4) (input logic clk, input logic enqueue, input int dataIn, output logic enqueued);
  mailbox #(.WIDTH(32), .SIZE(S)) scopeQueue;
  always_ff @(posedge clk) begin
    if (enqueue) begin
      scopeQueue.put(dataIn);
      enqueued <= 1;
    end else begin
      enqueued <= 0;
    end
  end
endmodule
module ThreadScope_Wait (input logic clk, input logic waitTrigger, output logic waited);
  always_ff @(posedge clk) begin
    if (waitTrigger)
      waited <= 1;
    else
      waited <= 0;
  end
endmodule
module ClassInstProc (input logic clk, input logic trigger, output logic done);
  class MyClass;
    int v;
    function new();
      v = 0;
    endfunction
    function void inc();
      v = v + 1;
    endfunction
    function int get();
      return v;
    endfunction
  endclass
  MyClass inst;
  always_ff @(posedge clk) begin
    if (trigger) begin
      inst = new();
      inst.inc();
      done <= (inst.get() != 0);
    end
  end
endmodule
