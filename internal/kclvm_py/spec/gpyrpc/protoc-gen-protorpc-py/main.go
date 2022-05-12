package main

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"text/template"

	plugin "github.com/chai2010/protorpc/protoc-gen-plugin"
	"github.com/golang/protobuf/protoc-gen-go/descriptor"
	"github.com/golang/protobuf/protoc-gen-go/generator"
)

func init() {
	plugin.RegisterCodeGenerator(new(protorpcPlugin))
}

func main() {
	if len(os.Args) > 1 && (os.Args[1] == "-h" || os.Args[1] == "-help") {
		fmt.Println("usage: protoc-gen-protorpc-py")
		fmt.Println("  # install protoc")
		fmt.Println("  go install github.com/golang/protobuf/protoc-gen-go")
		fmt.Println("  go install github.com/chai2010/protorpc/protoc-gen-protorpc")
		fmt.Println("  # install protoc-gen-protorpc-py")
		fmt.Println("  protoc --protorpc-py_out=. gpyrpc.proto")
		fmt.Println("  protoc-gen-protorpc-py -h")
		return
	}
	plugin.Main()
}

type protorpcPlugin struct{}

func (p *protorpcPlugin) Name() string        { return "protorpc-py" }
func (p *protorpcPlugin) FileNameExt() string { return ".pb.protorpc.py" }

func (p *protorpcPlugin) HeaderCode(g *generator.Generator, file *generator.FileDescriptor) string {
	moduleName := strings.TrimSuffix(filepath.Base(file.GetName()), ".proto") + "_pb2"

	var serviceList []*ServiceSpec
	for _, svc := range file.Service {
		serviceList = append(serviceList, p.buildServiceSpec(g, svc))
	}

	var messageMap = make(map[string]bool)
	for _, svc := range serviceList {
		for _, method := range svc.MethodList {
			messageMap[method.InputTypeName] = true
			messageMap[method.OutputTypeName] = true
		}
	}

	var messageList []string
	for k := range messageMap {
		messageList = append(messageList, k)
	}
	sort.Strings(messageList)

	var fnMap = template.FuncMap{
		"hello": func() string { return "hello" },
	}

	var buf bytes.Buffer
	t := template.Must(template.New("").Funcs(fnMap).Parse(tmpl))
	err := t.Execute(&buf,
		struct {
			G           *generator.Generator
			File        *generator.FileDescriptor
			ModuleName  string
			ServiceList []*ServiceSpec
			MessageList []string
		}{
			G:           g,
			File:        file,
			ModuleName:  moduleName,
			ServiceList: serviceList,
			MessageList: messageList,
		},
	)
	if err != nil {
		log.Fatal(err)
	}

	return buf.String()
}

func (p *protorpcPlugin) ServiceCode(g *generator.Generator, file *generator.FileDescriptor, svc *descriptor.ServiceDescriptorProto) string {
	return ""
}

func (p *protorpcPlugin) MessageCode(g *generator.Generator, file *generator.FileDescriptor, msg *descriptor.DescriptorProto) string {
	return ""
}

type ServiceSpec struct {
	ServiceName    string
	ServiceRawName string

	MethodList []ServiceMethodSpec
}

type ServiceMethodSpec struct {
	MethodName    string
	MethodRawName string

	InputTypeName  string
	OutputTypeName string
}

func (p *protorpcPlugin) buildServiceSpec(g *generator.Generator, svc *descriptor.ServiceDescriptorProto) *ServiceSpec {
	spec := &ServiceSpec{
		ServiceName:    generator.CamelCase(svc.GetName()),
		ServiceRawName: svc.GetName(),
	}

	for _, m := range svc.Method {
		if m.GetClientStreaming() || m.GetServerStreaming() {
			continue
		}
		spec.MethodList = append(spec.MethodList, ServiceMethodSpec{
			MethodName:    generator.CamelCase(m.GetName()),
			MethodRawName: m.GetName(),

			InputTypeName:  g.TypeName(g.ObjectNamed(m.GetInputType())),
			OutputTypeName: g.TypeName(g.ObjectNamed(m.GetOutputType())),
		})
	}

	return spec
}

const tmpl = `
{{- $G := .G -}}
{{- $File := .File -}}
{{- $ModuleName := .ModuleName -}}
{{- $ServiceList := .ServiceList -}}
{{- $MessageList := .MessageList -}}

# Code generated by protoc-gen-protorpc-py. DO NOT EDIT.
#
# plugin: https://github.com/chai2010/protorpc/protoc-gen-plugin
# plugin: https://github.com/chai2010/protorpc-py/protoc-gen-protorpc-py
#
# source: {{$File.GetName}}

import abc
import sys
import typing

from google.protobuf import message as _message

from .protorpc import ServiceMeta as _ServiceMeta
from .protorpc import Server as _Server

from .{{$ModuleName}} import ({{range $k, $v := $MessageList}}
    {{$v}},
{{- end}})

{{range $k, $svc := $ServiceList}}
class {{$svc.ServiceName}}(metaclass=abc.ABCMeta):
    {{- range $sss, $method := $svc.MethodList}}

    @abc.abstractmethod
    def {{$method.MethodName}}(self, args: {{$method.InputTypeName}}) -> {{$method.OutputTypeName}}:
        pass
    {{- end}}
{{end}}

{{range $k, $svc := $ServiceList}}
class {{$svc.ServiceName}}_Meta(_ServiceMeta):

    def __init__(self, instance: {{$svc.ServiceName}}):
        super().__init__()
        self._instance = instance

    def get_service_name(self) -> str:
        return "{{$svc.ServiceName}}"

    def get_method_list(self) -> typing.List[str]:
        return [
            {{- range $_, $method := $svc.MethodList}}
            "{{$method.MethodRawName}}",
            {{- end}}
        ]

    def create_method_req_message(self, method: str) -> _message.Message:
        {{- range $_, $method := $svc.MethodList}}
        if method in ["{{$method.MethodRawName}}", "{{$svc.ServiceName}}.{{$method.MethodRawName}}"]:
            return {{$method.InputTypeName}}()
        {{- end}}
        raise Exception(f"unknown method: {method}")

    def create_method_resp_message(self, method: str) -> _message.Message:
        {{- range $_, $method := $svc.MethodList}}
        if method in ["{{$method.MethodRawName}}", "{{$svc.ServiceName}}.{{$method.MethodRawName}}"]:
            return {{$method.OutputTypeName}}()
        {{- end}}
        raise Exception(f"unknown method: {method}")

    def get_service_instance(self) -> _message.Message:
        return typing.cast(_message.Message, self._instance)

    def call_method(self, method: str, req: _message.Message) -> _message.Message:
        {{- range $_, $method := $svc.MethodList}}
        if method in ["{{$method.MethodRawName}}", "{{$svc.ServiceName}}.{{$method.MethodRawName}}"]:
            return self._instance.{{$method.MethodName}}(req)
        {{- end}}
        raise Exception(f"unknown method: {method}")
{{end}}

{{range $k, $svc := $ServiceList}}
class {{$svc.ServiceName}}_Server:
    def __init__(self, instance: {{$svc.ServiceName}}):
        self.instance = instance

    def run(self, *, stdin=sys.stdin, stdout=sys.stdout):
        rpc_server = _Server()
        rpc_server.register_service({{$svc.ServiceName}}_Meta(self.instance))
        rpc_server.run(stdin=stdin, stdout=stdout)
{{end}}
`